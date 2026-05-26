import Lean

/-!
# Let's build a simple term elaborator (part 2)

Goal:
  For a simplified Lean-like syntax for dependently type lambda calculus terms
  ("LilLean"), write a *term elaborator*, a function that converts that syntax
  into well-typed expressions.


-/

namespace LilLean

open Lean

namespace Parser
/-!
## Syntax definitions for terms
-/

/-- Represents a term of the LilLean language. -/
declare_syntax_cat lilterm

namespace LilTerm

/-
Special binding powers:
  lead := 1022
  arg := 1023
  max := 1024
-/

/-- Parentheses -/
syntax:max "(" lilterm ")" : lilterm

/-- Constants. Elaborates to either a local constant (from the local context)
or a global constant (from the environment). -/
syntax:max ident : lilterm

/-- Placeholders. Elaborates to a fresh metavariable. -/
syntax:max "_" : lilterm

/-- Numeric literals -/
syntax:max num : lilterm

/-- Applications -/
syntax:lead lilterm:max lilterm:arg+ : lilterm

/-- Explicit annotation. For function applications, `@f x y z` means
to ignore explicit/implicit binder annotations in the type of `f`.
For functions, `@fun x y z => ...` means to ignore explicit/implicit binder
annotations in the expected type. -/
syntax:max "@" lilterm:max : lilterm

syntax explicitBinder := "(" ident (" : " lilterm)? ")"
syntax implicitBinder := "{" ident (" : " lilterm)? "}"
syntax instImplicitBinder := "[" lilterm "]"
syntax funBinder := ident <|> explicitBinder <|> implicitBinder <|> instImplicitBinder

-- completely different
--   p → q
--   (p : _) → q
-- completely the same
--   fun p => ...
--   fun (p : _) => ..

/-- Functions -/
syntax:max "fun " funBinder+ " => " lilterm : lilterm

/-- Arrows -/
syntax:25 lilterm:25 " → " lilterm:25 : lilterm

syntax piExplicitBinder := "(" ident " : " lilterm ")"
syntax piImplicitBinder := "{" ident " : " lilterm "}"
syntax piBinder := piExplicitBinder <|> piImplicitBinder <|> instImplicitBinder

/-- Dependent function types -/
syntax:25 piBinder " → " lilterm:25 : lilterm

/-- `let` definitions -/
syntax:lead "let " ident (" : " lilterm)? " := " lilterm "; " lilterm : lilterm

/-- Type universe -/
syntax "Type" : lilterm
/-- Prop universe -/
syntax "Prop" : lilterm

/-- Type ascriptions -/
syntax:max "(" lilterm " : " lilterm ")" : lilterm

/-- Apologize to LilLean for not knowing how to fill in this term yet. -/
syntax:max "lilsorry" : lilterm

/-- Represents a tactic of the LilLean language. -/
declare_syntax_cat liltactic

/-- Synthesizes a term using tactics. -/
syntax:lead "by " sepBy1IndentSemicolon(liltactic) : lilterm

end LilTerm

end Parser



namespace Elab.LilTerm
/-!
## Elaborator for terms
-/

inductive SyntheticMVarKind where
  | typeClass
  | tactic -- for future use

structure SyntheticMVarDecl where
  stx : Syntax
  kind : SyntheticMVarKind

structure Context where
  /-- When true, elaboration errors are logged, and `sorry` is used
  as a placeholder for terms that fail to elaborate. -/
  errToSorry : Bool := true

structure State where
  syntheticMVars : MVarIdMap SyntheticMVarDecl := {}
  pendingMVars : List MVarId := []

/--
LilTerm elaboration monad. Built on top of `MetaM` (for `isDefEq`, local
contexts, etc.), and keeps track of some additional state.
-/
abbrev TM := ReaderT Context (StateRefT State MetaM)

def throwUnknownSyntax {α : Type} : TM α :=
  throwError "Unknown syntax"

/--
Elaborates an identifier to either a local constant (an `Expr.fvar`)
or a global constant (an `Expr.const`).
-/
def elabConst (id : Ident) : TM Expr := do
  let c := id.getId
  let lctx ← getLCtx
  let env ← getEnv
  if let some localDecl := lctx.findFromUserName? c then
    return Expr.fvar localDecl.fvarId
  else if let some constVal := env.findConstVal? c.eraseMacroScopes then
    -- Instantiate the constant's universe levels with fresh
    -- level metavariables.
    let us ← constVal.levelParams.mapM (fun _ => Meta.mkFreshLevelMVar)
    return Expr.const constVal.name us
  else
    throwErrorAt id "Unknown constant `{c}`"

structure BinderView where
  name : Name
  type? : Option Syntax
  info : BinderInfo

def elabPiBinder (binder : Syntax) : TM BinderView := do
  match binder with
  | `(Parser.LilTerm.piBinder| ($name : $ty)) =>
    return { name := name.getId, type? := ty, info := .default }
  | `(Parser.LilTerm.piBinder| {$name : $ty}) =>
    return { name := name.getId, type? := ty, info := .implicit }
  | `(Parser.LilTerm.piBinder| [$ty]) =>
    let instName ← Core.mkFreshUserName `inst
    return { name := instName, type? := ty, info := .instImplicit }
  | _ => withRef binder throwUnknownSyntax

def elabFunBinder (binder : Syntax) : TM BinderView := do
  match binder with
  | `(Parser.LilTerm.funBinder| $name:ident) =>
    return { name := name.getId, type? := none, info := .default }
  | `(Parser.LilTerm.funBinder| ($name $[: $ty?]?)) =>
    return { name := name.getId, type? := ty?, info := .default }
  | `(Parser.LilTerm.funBinder| {$name $[: $ty?]?}) =>
    return { name := name.getId, type? := ty?, info := .implicit }
  | `(Parser.LilTerm.funBinder| [$ty]) =>
    let instName ← Core.mkFreshUserName `inst
    return { name := instName, type? := ty, info := .instImplicit }
  | _ => withRef binder throwUnknownSyntax

def elabSorry (expectedType? : Option Expr) (synthetic : Bool := false) :
    TM Expr := do
  let ty ← expectedType?.getDM Meta.mkFreshTypeMVar
  let u ← Meta.getLevel ty
  return mkApp2 (Expr.const ``sorryAx [u]) ty (toExpr synthetic)

mutual

/--
Elaborator for `lilterm` syntax. Frontend for `elabLilTermCore` that
handles the `errToSorry` feature.
-/
partial def elabLilTerm (t : Syntax) (expectedType? : Option Expr) :
    TM Expr := withRef t do
  try
    elabLilTermCore t expectedType?
  catch ex =>
    if (← read).errToSorry then
      Elab.logException ex
      elabSorry expectedType? (synthetic := true)
    else
      throw ex

/--
Core elaborator for `lilterm` syntax.
-/
partial def elabLilTermCore (t : Syntax) (expectedType? : Option Expr) :
    TM Expr := withRef t do
  match t with
  | `(lilterm| ($t')) =>
    elabLilTerm t' expectedType?
  | `(lilterm| Type) =>
    return Expr.sort (Level.succ Level.zero)
  | `(lilterm| Prop) =>
    return Expr.sort Level.zero
  | `(lilterm| _) =>
    Meta.mkFreshExprMVar expectedType?
  | `(lilterm| lilsorry) =>
    elabSorry expectedType?
  | `(lilterm| ($t' : $ty)) =>
    let tyE ← elabLilTermType ty
    elabLilTermEnsuringType t' (some tyE)
  | `(lilterm| $n:num) =>
    let v := n.getNat
    return mkNatLit v
  | `(lilterm| $ty1 → $ty2) =>
    let ty1E ← elabLilTermType ty1
    let ty2E ← elabLilTermType ty2
    return Expr.forallE `_a ty1E ty2E .default
  | `(lilterm| $b:piBinder → $ty2) =>
    let view ← elabPiBinder b
    let dom ← elabLilTermType? view.type?
    Meta.withLocalDecl view.name view.info dom fun domFVar => do
      let ty2E ← elabLilTermType ty2
      Meta.mkForallFVars #[domFVar] ty2E
  | `(lilterm| fun $binders* => $body) =>
    let views ← binders.mapM elabFunBinder
    elabFun views body expectedType? (explicit := false)
  | `(lilterm| @fun $binders* => $body) =>
    let views ← binders.mapM elabFunBinder
    elabFun views body expectedType? (explicit := true)
  | `(lilterm| @$f:ident) =>
    let fe ← elabConst f
    elabAppFn fe #[] expectedType? (explicit := true)
  | `(lilterm| $f:ident) =>
    let fe ← elabConst f
    elabAppFn fe #[] expectedType? (explicit := false)
  | `(lilterm| @$f:lilterm $args*) =>
    let fe ← elabLilTerm f none
    elabAppFn fe args expectedType? (explicit := true)
  | `(lilterm| $f:lilterm $args*) =>
    let fe ← elabLilTerm f none
    elabAppFn fe args expectedType? (explicit := false)
  | _ => throwUnknownSyntax

/--
Elaborates `t` and then ensures that its type is `expectedType?`, if present.
-/
partial def elabLilTermEnsuringType (t : Syntax) (expectedType? : Option Expr) :
    TM Expr := do
  let e ← elabLilTerm t expectedType?
  if let some expectedType := expectedType? then
    --logInfo m!"ensuring {e} has type {expectedType}"
    let eTy ← Meta.inferType e
    unless ← Meta.isDefEq eTy expectedType do
      throwErrorAt t "Term{indentExpr e}\n\
        has type{indentExpr eTy}\n\
        but is expected to have type{indentExpr expectedType}"
  return e

/--
Elaborates `t`, ensuring that the result is a type.
-/
partial def elabLilTermType (t : Syntax) : TM Expr := do
  let e ← elabLilTerm t none
  discard <| withRef t <| Meta.getLevel e
  return e

/--
Elaborates the type using `elabLilTermType`, if the type is present,
and otherwise returns a fresh type metavariable.
-/
partial def elabLilTermType? (t? : Option Syntax) : TM Expr := do
  if let some t := t? then
    elabLilTermType t
  else
    Meta.mkFreshTypeMVar

/--
Elaborates a `fun` expression.
Uses the expected type.
-/
partial def elabFun (views : Array BinderView) (body : Syntax)
    (expectedType? : Option Expr) (explicit : Bool) :
    TM Expr := do
  throwError "elabFun unimplemented"

-- /--
-- Elaborates a function application; a frontend for `elabAppFn` that
-- recognizes the `@` modifier.
-- -/
-- partial def elabApp (f : Syntax) (args : Array Syntax)
--     (expectedType? : Option Expr) :
--     TM Expr := do
--   match f with
--   | `(lilterm| @$f':lilterm) =>
--     elabAppFn f' args expectedType? (explicit := true)
--   | _ =>
--     elabAppFn f args expectedType? (explicit := false)

/--
Elaborates a function application `f args...` or `@f args...`

When `explicit := false` (no `@`), expands `args`, inserting metavariables
for implicit arguments.
Rule: implicit arguments are processed until the first explicit argument
that is not provided.

Additionally, the expected type is *propagated*.
-/
partial def elabAppFn (f : Expr) (args : Array Syntax)
    (expectedType? : Option Expr) (explicit : Bool) :
    TM Expr := do
  loop (← Meta.inferType f) f args.toList
where
  loop (eType : Expr) (e : Expr) (args : List Syntax) :
      TM Expr := do
    let eType ← Meta.whnfForall eType
    if let .forallE _ paramType eType' paramInfo := eType then
      if paramInfo.isExplicit || explicit then
        match args with
        | [] =>
          return e
        | arg::args' =>
          -- logInfo m!"explicit, {paramType}, {arg}"
          let arge ← elabLilTermEnsuringType arg paramType
          -- DTT: need to instantiate `bvar 0` with the argument
          let eType' := eType'.instantiate1 arge
          loop eType' (Expr.app e arge) args'
      else
        match paramInfo with
        | .implicit =>
          let arge ← Meta.mkFreshExprMVar paramType
          let eType' := eType'.instantiate1 arge
          loop eType' (Expr.app e arge) args
        | _ => throwError "no support for {repr paramInfo}"
    else if !args.isEmpty then
      throwError "have {args.length} argument(s), but not a function:\
        {indentExpr e}"
    else
      return e

end

end Elab.LilTerm

elab tk:"#elab_lilterm " t:lilterm : command => do
  Elab.Command.liftTermElabM do
    let e ← Elab.LilTerm.elabLilTerm t none |>.run {} |>.run' {}
    if e.hasSyntheticSorry then
      logInfoAt tk m!"elaborated with logged errors\n{e}"
    else
      logInfoAt tk m!"{e}"

#elab_lilterm Type
#elab_lilterm Prop
#elab_lilterm (Prop)
#elab_lilterm _
#elab_lilterm lilsorry
#elab_lilterm (lilsorry : Type)
#elab_lilterm 5
#elab_lilterm (_ : 5)
#elab_lilterm (Type : Type)
#elab_lilterm id
#elab_lilterm id 5
#elab_lilterm Type → Type
#elab_lilterm {p : Prop} → {q : Prop} → p → q → p
#elab_lilterm {p : Prop} → {q : Prop} → p → qq → p

#elab_lilterm (p : Type) → (q : Type) → p → q
/- What happens?
We elaborate `Type`
then we add `p : Type` to the local context (as `Expr.fvar fvar1`)
  we elaborate `Type
  then we add `q : Type` to the local context (as `Expr.fvar fvar2`)
    we elaborate `p`, getting `Expr.fvar fvar1`
    we elaborate `q`, getting `Expr.fvar fvar2`
    we construct `p → q` type, getting
      `Expr.forallE _ (Expr.fvar fvar1) (Expr.fvar fvar2) .default`
    then abstract `q`, getting
      `Expr.forallE _ (Expr.fvar fvar1) (.bvar 1) .default`
    then construct `(q : Type) → p → q`, getting
      `Expr.forallE _
        (Expr.sort levelOne)
        (Expr.forallE _ (Expr.fvar fvar1) (.bvar 1) .default)`
  then abstracting `p`, getting
    `Expr.forallE _
      (Expr.sort levelOne)
      (Expr.forallE _ (.bvar 1) (.bvar 1) .default)`
  then construct `(p : Type) → (q : Type) → p → q`, getting
    `Expr.forallE _
      (Expr.sort levelOne)
      (Expr.forallE _
        (Expr.sort levelOne)
        (Expr.forallE _ (.bvar 1) (.bvar 1) .default))`
-/

#elab_lilterm (f : Nat → Type) → (n : Nat) → f n → f (Nat.add n 1)

example : {n : Nat} → Fin n → Fin n := fun x => x

def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
def Injective' (f : α → β) : Prop :=
  ∀ {a₁ a₂}, f a₁ = f a₂ → a₁ = a₂

variable (h1 : Injective id) (h2 : Injective' id)
#check h1
#check h2

end LilLean
