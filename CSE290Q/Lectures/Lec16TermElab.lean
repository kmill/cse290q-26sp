import Lean

/-!
# Let's build a simple term elaborator (part 3)

Goal:
  For a simplified Lean-like syntax for dependently type lambda calculus terms
  ("LilLean"), write a *term elaborator*, a function that converts that syntax
  into well-typed expressions.

Last time: implemented `elabAppFn` for function application elaboration.

TODO:
- expected type propagation for `elabAppFn`
- eliminator support for `elabAppFn`
- `fun` elaboration
- `⟨...⟩` anonymous constructor elaboration
- creating a lil tactic system
- typeclass inference

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
syntax:lead lilterm:max (ppSpace lilterm:arg)+ : lilterm

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
    -- level metavariables. (Like polytype instantiation in System F.)
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

structure ElabAppFnState where
  motive? : Option MVarId := none
  postponed : Array (MVarId × Syntax) := #[]

abbrev AppM := StateRefT ElabAppFnState TM

/--
Elaborates a function application `f args...` or `@f args...`

When `explicit := false` (no `@`), expands `args`, inserting metavariables
for implicit arguments.
Rule: implicit arguments are processed until the first explicit argument
that is not provided.

Additionally, the expected type is *propagated*.
Design constraints:
- we want propagation to *not* solve for arguments that have been explicitly
  provided, before those arguments are actually elaborated.
  Why? We want to be sure that the expressions obtained from elaboration
  match user expectations.
- we want propagation to avoid needing to do unnecessary higher-order
  unifications.  (that means `?m x y z =?= e`)
-/
partial def elabAppFnAux
    (elabLilTermEnsuringType : Syntax → Option Expr → TM Expr)
    (f : Expr) (args : Array Syntax)
    (expectedType? : Option Expr) (explicit : Bool) :
    TM Expr := do
  -- logInfo m!"elaborating {f} with expected type {expectedType?}"
  loop (← Meta.inferType f) f args.toList expectedType? |>.run' {}
where
  addArg (eTypeBody e arge : Expr) (args : List Syntax)
      (expectedType? : Option Expr) :
      AppM Expr := do
    -- DTT: need to instantiate `bvar 0` with the argument
    let eTypeBody' := eTypeBody.instantiate1 arge
    loop eTypeBody' (Expr.app e arge) args expectedType?
  finalize (e : Expr) (expectedType? : Option Expr) : AppM Expr := do
    if let some expectedType := expectedType? then
      -- Hint for the type of `e` to be `expectedType`
      discard <| Meta.isDefEq (← Meta.inferType e) expectedType
    for (mvarId, arg) in (← get).postponed do
      let arge ← elabLilTermEnsuringType arg (← mvarId.getType)
      if (← occursCheck mvarId arge) then
        mvarId.assign arge
      else
        throwError "occurs check failed"
    return e
  loop (eType : Expr) (e : Expr) (args : List Syntax)
      (expectedType? : Option Expr) :
      AppM Expr := do
    let eType' ← Meta.whnf eType
    if let .forallE _ paramType eTypeBody paramInfo := eType' then
      --isMotiveParam eType'
      if paramInfo.isExplicit || explicit then
        match args with
        | [] =>
          finalize e expectedType?
        | arg::args' =>
          -- logInfo m!"explicit, {paramType}, {arg}"
          let expectedType? ←
            if let some expectedType := expectedType? then
              if let some resultingType ← resultingType? eType args then
                if ← Meta.isDefEq resultingType expectedType then
                  -- logInfo m!"propagated expected type {expectedType}, \
                  --   current expression is now{indentExpr e}"
                  pure none
                else
                  pure expectedType?
              else
                pure expectedType?
            else
              pure none
          let arge ← elabLilTermEnsuringType arg paramType
          addArg eTypeBody e arge args' expectedType?
      else
        match paramInfo with
        | .implicit =>
          let arge ← Meta.mkFreshExprMVar paramType
          addArg eTypeBody e arge args expectedType?
        | _ => throwError "no support for {repr paramInfo}"
    else if !args.isEmpty then
      throwError "have {args.length} argument(s), but not a function:\
        {indentExpr e}"
    else
      finalize e expectedType?
  /--
  Computes what the expected type of the function would be, without
  actually elaborating any of the arguments in `args`.
  The computation can fail if the result depends on the arguments.

  The `eType` type may have loose bvars.
  -/
  resultingType? (eType : Expr) (args : List Syntax) : TM (Option Expr) := do
    let eType' ← if eType.hasLooseBVars then pure eType else Meta.whnf eType
    if let .forallE _ _paramType eTypeBody paramInfo := eType' then
      if paramInfo.isExplicit || explicit then
        match args with
        | [] =>
          finalizeResultingType? eType
        | _::args' =>
          resultingType? eTypeBody args'
      else
        match paramInfo with
        | .implicit =>
          resultingType? eTypeBody args
        | _ => return none
    else if !args.isEmpty then
      return none
    else
      finalizeResultingType? eType
  finalizeResultingType? (eType : Expr) : TM (Option Expr) := do
    if eType.hasLooseBVars then
      return none
    else
      return eType
  isMotiveParam (eType : Expr) (args : List Syntax) (depth : Nat) : TM Bool := do
    let eType' ← if eType.hasLooseBVars then pure eType else Meta.whnf eType
    if let .forallE _ _paramType eTypeBody paramInfo := eType' then
      if paramInfo.isExplicit || explicit then
        match args with
        | [] =>
          finalizeGetMotive? eType depth
        | _::args' =>
          isMotiveParam eTypeBody args' (depth + 1)
      else
        match paramInfo with
        | .implicit =>
          isMotiveParam eTypeBody args (depth + 1)
        | _ => return false
    else if !args.isEmpty then
      return false
    else
      finalizeGetMotive? eType depth
  finalizeGetMotive? (eType : Expr) (depth : Nat) : TM Bool := do
    return eType.isApp && eType.getAppFn == Expr.bvar depth

#exit

mutual

/--
Elaborator for `lilterm` syntax. Frontend for `elabLilTermCore` that
handles the `errToSorry` feature.
-/
partial def elabLilTerm (t : Syntax) (expectedType? : Option Expr) :
    TM Expr := withRef t do
  -- logInfo m!"elabLilTerm{indentD t}\nwith expected type {expectedType?}"
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
Elaborates `t` and then ensures that its type is `expectedType?`, if given.
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

TODO: handle `explicit` and expected type binder infos.
-/
partial def elabFun (views : Array BinderView) (body : Syntax)
    (expectedType? : Option Expr) (explicit : Bool) :
    TM Expr := do
  loop #[] views.toList expectedType?
where
  loop (fvars : Array Expr) (views : List BinderView)
      (expectedType? : Option Expr) : TM Expr := do
    match views with
    | [] =>
      let e ← elabLilTerm body expectedType?
      Meta.mkLambdaFVars fvars e
    | view::views' =>
      let dom ← elabLilTermType? view.type?
      Meta.withLocalDecl view.name view.info dom fun fvar => do
        let expectedType?' ←
          if let some expectedType := expectedType? then
            let expectedType ← Meta.whnf expectedType
            if let .forallE _ t b _ := expectedType then
              if ← Meta.isDefEq dom t then
                pure <| some <| b.instantiate1 fvar
              else
                pure none
            else
              pure none
          else
            pure none
        loop (fvars.push fvar) views' expectedType?'

partial def elabAppFn
    (f : Expr) (args : Array Syntax)
    (expectedType? : Option Expr) (explicit : Bool) :
    TM Expr := do
  elabAppFnAux elabLilTermEnsuringType f args expectedType? explicit

end

end Elab.LilTerm

#reduce (types := true) IO Nat

#check let f := @id; (f true, f "yo")
#check let f := id; (f true, f "yo")

#check id id id id id id true

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
#elab_lilterm @id
#elab_lilterm id
#elab_lilterm id 5
#elab_lilterm (id (id 5) : Nat)
#elab_lilterm Type → Type
#elab_lilterm {p : Prop} → {q : Prop} → p → q → p
#elab_lilterm {p : Prop} → {q : Prop} → p → qq → p

#elab_lilterm (p : Type) → (q : Type) → p → q

#elab_lilterm (f : Nat → Type) → (n : Nat) → f n → f (Nat.add n 1)

#elab_lilterm fun (n : Nat) => Nat.succ n
#elab_lilterm fun {β : Type} => fun (x : β) => x
#elab_lilterm fun {β : Type} (x : β) => x

#elab_lilterm Bool.true 5

#check Nat.add
#check (fun n => Nat.rec rfl (fun n' h => congrArg Nat.succ h) n :
  (n : Nat) → Eq (Nat.add 0 n) n)
#elab_lilterm (fun n => Nat.rec rfl (fun n' h => congrArg Nat.succ h) n :
  (n : Nat) → Eq (Nat.add 0 n) n)
#elab_lilterm (fun n => Nat.recOn n rfl (fun n' h => congrArg Nat.succ h) :
  (n : Nat) → Eq (Nat.add 0 n) n)

example : {n : Nat} → Fin n → Fin n := fun x => x

def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
def Injective' (f : α → β) : Prop :=
  ∀ {a₁ a₂}, f a₁ = f a₂ → a₁ = a₂

variable (h1 : Injective id) (h2 : Injective' id)
#check h1
#check h2

end LilLean
