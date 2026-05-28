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
Monad for traversing expressions.
The handle types `ℓ` and `ε` are determined by the monad `m`.
-/
class MonadGetExpr (m : Type → Type) (ℓ ε : outParam Type)
    extends MonadGetLevel m ℓ where
  /-- Gets the expression referred to by the handle `ε`. -/
  getExpr (e : ε) : m (Expr ℓ ε)
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
  exprHash (u : ε) : m UInt64

export MonadGetExpr (getExpr exprHash)

/--
Monad for constructing expressions.
The handle types `ℓ` and `ε` are determined by the monad `m`.
-/
class MonadMkExpr (m : Type → Type) (ℓ ε : outParam Type)
    extends MonadMkLevel m ℓ where
  mkExprBVar (idx : Nat) : m ε
  mkExprFVar (fvarId : FVarId) : m ε
  mkExprMVar (mvarId : MVarId) : m ε
  mkExprSort (u : ℓ) : m ε
  mkExprConst (declName : Name) (us : List ℓ) : m ε
  mkExprApp (fn : ε) (arg : ε) : m ε
  mkExprLam (binderName : Name) (binderType : ε) (body : ε)
    (binderInfo : BinderInfo) : m ε
  mkExprPi (binderName : Name) (binderType : ε) (body : ε)
    (binderInfo : BinderInfo) : m ε
  mkExprLet (declName : Name) (type : ε) (value : ε) (body : ε) : m ε
  mkExprLit (l : Literal) : m ε
  mkExprProj (typeName : Name) (idx : Nat) (struct : ε) : m ε

export MonadMkExpr
  (mkExprBVar mkExprFVar mkExprSort mkExprMVar mkExprConst mkExprApp mkExprLam
    mkExprPi mkExprLet mkExprLit mkExprProj)

instance (ℓ ε m n) [MonadLift m n] [MonadGetExpr m ℓ ε] :
    MonadGetExpr n ℓ ε where
  getExpr e := liftM (getExpr e : m _)
  exprHash e := liftM (exprHash e : m _)

instance (ℓ ε m n) [MonadLift m n] [MonadMkExpr m ℓ ε] :
    MonadMkExpr n ℓ ε where
  mkExprBVar idx := liftM (mkExprBVar idx : m _)
  mkExprFVar fvarId := liftM (mkExprFVar fvarId : m _)
  mkExprMVar mvarId := liftM (mkExprMVar mvarId : m _)
  mkExprSort u := liftM (mkExprSort u : m _)
  mkExprConst declName us := liftM (mkExprConst declName us : m _)
  mkExprApp fn arg := liftM (mkExprApp fn arg : m _)
  mkExprLam n t b i := liftM (mkExprLam n t b i : m _)
  mkExprPi n t b i := liftM (mkExprPi n t b i : m _)
  mkExprLet n t b v := liftM (mkExprLet n t b v : m _)
  mkExprLit l := liftM (mkExprLit l : m _)
  mkExprProj n i s := liftM (mkExprProj n i s : m _)

inductive BindingKind
  | lam
  | pi

def BindingKind.mk {ℓ ε m} [MonadMkExpr m ℓ ε]
    (kind : BindingKind)
    (binderName : Name) (binderType : ε) (body : ε)
    (binderInfo : BinderInfo) : m ε :=
  match kind with
  | .lam => mkExprLam binderName binderType body binderInfo
  | .pi => mkExprPi binderName binderType body binderInfo

end LilLean
