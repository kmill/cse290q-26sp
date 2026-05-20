import Lean

/-!
# Let's build a simple term elaborator

Goal:
  For a simplified Lean-like syntax for dependently type lambda calculus terms
  ("LilLean"), write a *term elaborator*, a function that converts that syntax
  into well-typed expressions.

We will make use of the following facilities in Lean for this version:
- `Lean.Expr` for the well-typed expressions
- `Lean.Syntax` is the data structure for syntax, making use of
  the `syntax` command to define parsers and syntax kinds, as well
  as the syntax quotation system for matching and constructing syntax
- `whnf`, `isDefEq`, metavariable contexts, local contexts, and other core Lean
  datatypes and algorithms

What's in scope is defining
1. The syntax of our language (using `syntax`)
2. The elaboration function
  `elabLilTerm (t : Syntax) (expectedType? : Option Expr) : TM Expr`

where `TM` is our monad for term elaboration.


## Bidirectional typechecking/elaboration

Example:
  id : {α : Type} → α → α

  Suppose our local context has `x : ?_` (a variable with an unknown type)

  elabLilTerm `(id x) (some Nat)
    Elaborating function applications
    We take `id` and apply metavariables for all arguments
    1. `{α : Type}` parameter, let's use `?m.1 : Type` as the argument
    2. `α` parameter, let's use `?m.2 : ?m.1` as the argument
    so, so far we have `@id ?m.1 ?m.2 : ?m.1`.

    Given that the expected type is `Nat`, we can unify `?m.1` with `Nat`,
    assigns `?m.1 := Nat`.
    So, now we have `@id Nat ?m.2 : Nat`, and `?m.2 : Nat`.

    Now let's look at the actual arguments. The argument `x` is passed
    as argument number 2. We need to elaborate this
    elabLilTerm `(x) (some Nat)
    We resolve the identifier `x`, which is `x : ?_` in the local context
    and then we can try unifying `?_` with `Nat`, and so we get `x : Nat`
    This returns `x`.
    Then, we assign `?m.2 := x`.

    The result is `@id Nat x`, which has type `Nat`.

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

/-- Constants -/
syntax:max ident : lilterm

/-
lilterm ::= "(" lilterm ")"
          | ident
          | "_"
          | lilterm lilterm+
-/

/-- Placeholders -/
syntax:max "_" : lilterm

/-- Numeric literals -/
syntax:max num : lilterm

/-- Applications -/
syntax:lead lilterm:max lilterm:arg+ : lilterm
/-!
What are binding powers?
Lean uses Pratt parsing.
-/

/-- Explicit annotation -/
syntax:max "@" lilterm:max : lilterm

#check `(lilterm| f @id (@g x y z))

syntax explicitBinder := "(" ident (" : " lilterm)? ")"
syntax implicitBinder := "{" ident (" : " lilterm)? "}"
syntax instImplicitBinder := "[" lilterm "]"
syntax funBinder := ident <|> explicitBinder <|> implicitBinder <|> instImplicitBinder

/-- Functions -/
syntax:max "fun " funBinder+ " => " lilterm : lilterm

--#check `(lilterm| f x y fun a (n : Nat) => a)

/-- Arrows -/
syntax:25 lilterm:25 " → " lilterm:25 : lilterm

syntax piExplicitBinder := "(" ident " : " lilterm ")"
syntax piImplicitBinder := "{" ident " : " lilterm "}"
syntax piBinder := piExplicitBinder <|> piImplicitBinder <|> instImplicitBinder

/-- Dependent function types -/
syntax:25 piBinder " → " lilterm:25 : lilterm

-- #check `(lilterm| (n : Nat) → Fin n)
-- #check `(lilterm| {n : Nat} → Fin n)
-- #check `(lilterm| [Add α] → (x : α) → (y : α) → Eq (add x y) (add y x))

/-- `let` definitions -/
syntax:lead "let " ident (" : " lilterm)? " := " lilterm "; " lilterm : lilterm

-- #check `(lilterm| let x := 3; f x)
-- #check `(lilterm| let x : Nat := 3; f x)

/-- Type universe -/
syntax "Type" : lilterm
/-- Prop universe -/
syntax "Prop" : lilterm

/-- Type ascriptions -/
syntax:max "(" lilterm " : " lilterm ")" : lilterm

-- #check `(lilterm| (@id : {α : Type} → α → α))
-- #check `(lilterm| (id : _ → _))

/-- Apologize to LilLean for not knowing how to fill in this term yet. -/
syntax:max "sorry" : lilterm

syntax:lead "by " tacticSeq : lilterm

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

structure State where
  syntheticMVars : MVarIdMap SyntheticMVarDecl := {}
  pendingMVars : List MVarId := []

/--
LilTerm elaboration monad. Built on top of `MetaM` (for `isDefEq`, local
contexts, etc.), and keeps track of some additional state.
-/
abbrev TM := StateRefT State MetaM

def elabConst (id : Ident) : TM Expr := do
  let c := id.getId.eraseMacroScopes
  let lctx ← getLCtx
  let env ← getEnv
  if let some localDecl := lctx.findFromUserName? c then
    return Expr.fvar localDecl.fvarId
  else if let some constVal := env.findConstVal? c then
    let us ← constVal.levelParams.mapM (fun _ => Meta.mkFreshLevelMVar)
    return Expr.const c us
  else
    throwError "Unknown constant `{c}`"

mutual
/--
Elaborator for `lilterm` syntax.
-/
partial def elabLilTerm (t : Syntax) (expectedType? : Option Expr) :
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
  | `(lilterm| sorry) =>
    let ty ←
      if let some expectedType := expectedType? then
        pure expectedType
      else
        Meta.mkFreshTypeMVar
    let u ← Meta.getLevel ty
    return Expr.app (Expr.app (Expr.const ``sorryAx [u]) ty) (Expr.const ``false [])
  | `(lilterm| ($t' : $ty)) =>
    let tyE ← elabLilTermType ty
    elabLilTermEnsuringType t' (some tyE)
  | `(lilterm| $n:num) =>
    let v := n.getNat
    return mkNatLit v
  | `(lilterm| $id:ident) =>
    elabConst id
  | `(lilterm| $ty1 → $ty2) =>
    let ty1E ← elabLilTermType ty1
    let ty2E ← elabLilTermType ty2
    return Expr.forallE `_a ty1E ty2E .default
  | `(lilterm| $b:piBinder → $ty2) =>
    let (name, ty1, bi) ←
      match b with
      | `(Parser.LilTerm.piBinder| ($name : $ty)) => pure (name.getId, ty, BinderInfo.default)
      | `(Parser.LilTerm.piBinder| {$name : $ty}) => pure (name.getId, ty, BinderInfo.implicit)
      | `(Parser.LilTerm.piBinder| [$ty]) => pure (`_inst, ty, BinderInfo.instImplicit)
      | _ => Elab.throwUnsupportedSyntax
    let name := name.eraseMacroScopes
    let ty1E ← elabLilTermType ty1
    Meta.withLocalDecl name bi ty1E fun ty1FVar => do
      let ty2E ← elabLilTermType ty2
      Meta.mkForallFVars #[ty1FVar] ty2E
  | _ => throwError "Unknown syntax"

/--
Elaborates `t` and then ensures that its type is `expectedType?`, if present.
-/
partial def elabLilTermEnsuringType (t : Syntax) (expectedType? : Option Expr) :
    TM Expr := do
  let e ← elabLilTerm t expectedType?
  if let some expectedType := expectedType? then
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

end

end Elab.LilTerm

elab tk:"#elab_lilterm " t:lilterm : command => do
  Elab.Command.liftTermElabM do
    let e ← Elab.LilTerm.elabLilTerm t none |>.run' {}
    logInfoAt tk m!"{e}"

#elab_lilterm Type
#elab_lilterm Prop
#elab_lilterm (Prop)
#elab_lilterm _
#elab_lilterm sorry
#elab_lilterm (sorry : Type)
#elab_lilterm 5
#elab_lilterm (_ : 5)
#elab_lilterm (Type : Type)
#elab_lilterm id
#elab_lilterm Type → Type
#elab_lilterm {p : Prop} → {q : Prop} → p → q → p

end LilLean
