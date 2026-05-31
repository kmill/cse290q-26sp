/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import Lean

/-!
# Universe level expressions

See the discussion at the beginning of `LilLean.Expr.Types`. In LilLean, we
take an approach where expressions are represented as explicit directed acyclic
graphs, rather than using recursive types. Traversing level expressions requires
explicit dereferencing using a monadic operation.
-/

public section

namespace LilLean

export Lean (Name)

/--
Unique identifiers for universe level metavariables.
-/
structure LMVarId where
  id : Nat
  deriving Inhabited, DecidableEq, Hashable, Repr, Ord

/--
Universe level expression.

The type is non-recursive, and recursion is represented indirectly through
the `ℓ` type parameter, which represents a handle to a `Level`.

Note: One can make a recursive version of this type using
```
structure LevelR where
  level : Level LevelR
```
-/
inductive Level (ℓ : Type) where
  /-- Level `0`. -/
  | zero  : Level ℓ
  /-- `offset u c` represents `u + c`.
  (Lean 4 note: this is represented using `Level.succ` constructors instead.) -/
  | offset : ℓ → Nat → Level ℓ
  | max   : ℓ → ℓ → Level ℓ
  /-- `ipos u v` is `u` if `v` is nonzero, and otherwise it is `0`.
  This is used to implement impredicativity of `Prop`:
  given `α : Sort u` and `β : Sort v`,
  then `α → β : Sort (max (ipos u v) v)`.
  (Lean 4 note: instead there is `imax`, impredicative `max`. With that system,
  one has `α → β : imax u v`. With `ipos` we are able to compute normal forms
  due to its more flexible algebraic rules. Lean 4's level normalization
  procedure is incomplete in the presence of `imax` expressions.) -/
  | ipos  : ℓ → ℓ → Level ℓ
  /-- Level parameter. -/
  | param : Name → Level ℓ
  /-- Level metavariable. Solve for and instantiated as part of the elaboration
  process. -/
  | mvar  : LMVarId → Level ℓ
  deriving Inhabited

/--
Object packaging up the level context state, making it possible to create
a non-monadic interface for traversing level expressions.

The `Level'` type includes a `LevelGetter` as an inductive type parameter.

Normally an object like this is represented as a `class`
-/
structure LevelGetter (ℓ : Type) where
  /--
  Gets the level referred to by the handle `ℓ`.
  Returns `Level.zero` for invalid handles, and may panic.
  Should not return `Level.level`.
  -/
  get : ℓ → Level ℓ
  /--
  Returns a hash of the level, using `Level.hashCore`. Additionally,
  - Bit 0 is 1 iff the level has a `param`.
  - Bit 1 is 1 iff the level has an `mvar`.
  -/
  hash : ℓ → UInt64

/--
Monad for traversing level expressions.
The handle type `ℓ` is determined by the monad `m`.
-/
class MonadGetLevel (m : Type → Type) (ℓ : outParam Type) where
  getLevelGetter : m (LevelGetter ℓ)

export MonadGetLevel (getLevelGetter)

def getLevel {ℓ m} [Monad m] [MonadGetLevel m ℓ] (u : ℓ) : m (Level ℓ) :=
  return (← getLevelGetter).get u

def levelHash {ℓ m} [Monad m] [MonadGetLevel m ℓ] (u : ℓ) : m UInt64 :=
  return (← getLevelGetter).hash u

/--
Level handle that provides a functional interface to traverse its structure.
The `BEq` instance on this type computes *structural* `Level` equality,
rather than mere handle equality.

The `LevelGetter` is in the type itself as an inductive type parameter.
This is a way to conveniently thread this state through computations.
One can think of it as encoding a specific heap state in the type itself.

Be careful to avoid keeping references to a `Level'`, since it creates
non-linear uses of the underlying memory. E.g. the old `LevelContext` will
persist, and `LevelContext.mkLevel` will result in allocating new copies of
existing `LevelBlock`s. It's not a matter of correctness, just performance.
-/
structure Level' {ℓ : Type} (ctx : LevelGetter ℓ) where
  handle : ℓ

/--
Monad for constructing level expressions.
The handle type `ℓ` is determined by the monad `m`.
-/
class MonadMkLevel (m : Type → Type) (ℓ : outParam Type) where
  /-- Constructs a handle for the level expression. -/
  mkLevel : Level ℓ → m ℓ

export MonadMkLevel (mkLevel)

instance (ℓ m n) [MonadLift m n] [MonadGetLevel m ℓ] : MonadGetLevel n ℓ where
  getLevelGetter := liftM (getLevelGetter : m _)

instance (ℓ m n) [MonadLift m n] [MonadMkLevel m ℓ] : MonadMkLevel n ℓ where
  mkLevel u := liftM (mkLevel u : m _)

end LilLean
