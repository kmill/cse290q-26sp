/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Level.Types

/-!
# Expression type

In LilLean, we opt to take an approach where expressions are represented by
an explicit directed acyclic graph (DAG), rather than using a recursive type.
The reason for this is that we can demonstrate subexpression sharing, caching
values, and so on, without making use of special compiler features (e.g. using
the `@[computed_field]` attribute) or unsafe pointer comparison hacks.

A downside to this is that we cannot pattern match expressions so easily,
and accessing components of expressions requires monads. However, expression
sharing is clearer.
-/

public section

namespace LilLean

/-- Literal values for `Expr`. -/
inductive Literal where
  /-- Natural number literal -/
  | natVal (val : Nat)
  /-- String literal -/
  | strVal (val : String)
  deriving Inhabited, BEq, Hashable, Repr

inductive BinderInfo where
  /-- Default binder annotation, e.g. `(x : α)` -/
  | explicit
  /-- Implicit binder annotation, e.g., `{x : α}` -/
  | implicit
  /-- Lazy implicit binder annotation, e.g., `⦃x : α⦄` (called "strict implicit"
  in Lean 4) -/
  | lazyImplicit
  /-- Instance implicit binder annotation, e.g., `[Decidable α]` -/
  | instImplicit
  deriving Inhabited, BEq, Hashable, Repr

/--
Unique identifier to refer to expression metavariables.
-/
structure MVarId where
  name : Nat
  deriving Inhabited, BEq, Hashable, Repr

/--
Unique identifier to refer to free variables in the local context.
-/
structure FVarId where
  name : Nat
  deriving Inhabited, BEq, Hashable, Repr

/--
Type of expressions. This type is non-recursive, and recursion is represented
indirectly through the `ε` type, which represents a handle to an `Expr`.
The levels are represented indirectly through the `ℓ` type, which represents
a handle to a `Level`.

Note: One can make a recursive version of this type using
```
structure ExprR ℓ where
  expr : Expr ℓ ExprR
```
-/
inductive Expr (ℓ ε : Type) where
  | bvar (idx : Nat)
  | fvar (fvarId : FVarId)
  | mvar (mvarId : MVarId)
  | sort (u : ℓ)
  | const (declName : Name) (us : List ℓ)
  | app (fn : ε) (arg : ε)
  | lam (binderName : Name) (binderType : ε) (body : ε) (binderInfo : BinderInfo)
  | pi (binderName : Name) (binderType : ε) (body : ε) (binderInfo : BinderInfo)
  | «let» (declName : Name) (type : ε) (value : ε) (body : ε)
  | lit (l : Literal)
  | proj (typeName : Name) (idx : Nat) (struct : ε)

instance {ℓ ε} : Inhabited (Expr ℓ ε) := ⟨Expr.const `_default []⟩

/--
Object packaging up the level and expression context states, making it possible
to create a non-monadic interface for traversing expressions.

The `Expr'` type includes an `ExprGetter` as an inductive type parameter.
-/
structure ExprGetter (ℓ ε : Type) extends level : LevelGetter ℓ where
  /--
  Gets the expression referred to by the handle `ε`.
  Returns `default`, and may panic.
  Should not return `Level.level`.
  -/
  getExpr : ε → Expr ℓ ε
  /--
  Returns a hash of the expression, using `Expr.hashCore`. Additionally,
  - Bit 0 is 1 iff the expr has a level `param`.
  - Bit 1 is 1 iff the expr has a level `mvar`.
  - Bit 2 is 1 iff the expr has an `fvar`.
  - Bit 3 is 1 iff the expr has an `mvar`.
  - Bits 4-11 give the depth of the expression, saturated at 255
  - Bits 12-31 give the range of loose bvars
  - Bits 32-63 are the rest of the hash
  -/
  exprHash : ε → UInt64

/--
Monad for traversing expressions.
The handle types `ℓ` and `ε` are determined by the monad `m`.
-/
class MonadGetExpr (m : Type → Type) (ℓ ε : outParam Type)
    extends MonadGetLevel m ℓ where
  getExprGetter : m (ExprGetter ℓ ε)

export MonadGetExpr (getExprGetter)

def getExpr {ℓ ε m} [Monad m] [MonadGetExpr m ℓ ε] (e : ε) : m (Expr ℓ ε) :=
  return (← getExprGetter).getExpr e

def exprHash {ℓ ε m} [Monad m] [MonadGetExpr m ℓ ε] (e : ε) : m UInt64 :=
  return (← getExprGetter).exprHash e

/--
Expression handle that provides a functional interface to traverse its
structure. The `BEq` instance on this type computes *structural* `Expr`
equality, rather than mere handle equality. If `alpha` is true, then this
instance ignores binder names and binder info.

The `ExprGetter` is in the type itself as an inductive type parameter.
This is a way to conveniently thread this state through computations.
One can think of it as encoding a specific heap state in the type itself.

Like for `Level'`, be careful to avoid keeping references to a `Expr'`,
since it creates non-linear uses of the underlying memory. E.g. the old
`ExprContext` and `LevelContext` will persist, and `mkExpr` and `mkLevel` will
result in allocating new copies of existing `ExprBlock`s and `LevelBlock`s.
This is not a matter of correctness, just performance.
-/
structure Expr' {ℓ ε : Type} (ctx : ExprGetter ℓ ε) (alpha : Bool) where
  handle : ε

/--
Monad for constructing expressions.
The handle types `ℓ` and `ε` are determined by the monad `m`.
-/
class MonadMkExpr (m : Type → Type) (ℓ ε : outParam Type)
    extends MonadMkLevel m ℓ where
  /-- Constructs a handle for the expression. -/
  mkExpr : Expr ℓ ε → m ε

export MonadMkExpr (mkExpr)

instance (ℓ ε m n) [MonadLift m n] [MonadGetExpr m ℓ ε] :
    MonadGetExpr n ℓ ε where
  getExprGetter := liftM (getExprGetter : m _)

instance (ℓ ε m n) [MonadLift m n] [MonadMkExpr m ℓ ε] :
    MonadMkExpr n ℓ ε where
  mkExpr e := liftM (mkExpr e : m _)

end LilLean
