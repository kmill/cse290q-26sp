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

A consequence to this is that we cannot pattern match expressions so easily,
and accessing components of expressions requires monads.
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
The levels are represented indirectly through the `u` type, which represents
a handle to a `Level`.
-/
inductive Expr (ℓ ε : Type) where
  | bvar (idx : Nat)
  | fvar (fvarId : FVarId)
  | mvar (mvarId : MVarId)
  | sort (u : ℓ)
  | const (declName : Name) (us : List ℓ)
  | app (fn : Expr ℓ ε) (arg : Expr ℓ ε)
  | lam (binderName : Name) (binderType : Expr ℓ ε) (body : Expr ℓ ε) (binderInfo : BinderInfo)
  | pi (binderName : Name) (binderType : Expr ℓ ε) (body : Expr ℓ ε) (binderInfo : BinderInfo)
  | «let» (declName : Name) (type : Expr ℓ ε) (value : Expr ℓ ε) (body : Expr ℓ ε)
  | lit : Literal → Expr ℓ ε
  | proj (typeName : Name) (idx : Nat) (struct : Expr ℓ ε)

instance {ℓ ε} : Inhabited (Expr ℓ ε) := ⟨Expr.const `_default []⟩

end LilLean
