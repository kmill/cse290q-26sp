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
structure Level' where
  level : Level Level'
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
Monad for traversing level expressions.
The handle type `ℓ` is determined by the monad `m`.
-/
class MonadGetLevel (m : Type → Type) (ℓ : outParam Type) where
  /-- Gets the level referred to by the handle `ℓ`. -/
  getLevel (u : ℓ) : m (Level ℓ)
  /--
  Returns a hash of the level, using `Level.hashCore`. Additionally,
  - Bit 0 is 1 iff the level has a `param`.
  - Bit 1 is 1 iff the level has an `mvar`.
  -/
  levelHash (u : ℓ) : m UInt64

export MonadGetLevel (getLevel levelHash)

/--
Monad for constructing level expressions.
The handle type `ℓ` is determined by the monad `m`.
-/
class MonadMkLevel (m : Type → Type) (ℓ : outParam Type) where
  /-- Makes `Level.zero`. -/
  mkLevelZero : m ℓ
  /-- `mkLevelOffset u n` makes `Level.offset u n`. Returns `u` if `n = 0`. -/
  mkLevelOffset : ℓ → Nat → m ℓ
  /-- Makes `Level.max u v`. -/
  mkLevelMax : ℓ → ℓ → m ℓ
  /-- Makes `Level.ipos u v`. This represents `if v > 0 then u else 0`. -/
  mkLevelIPos : ℓ → ℓ → m ℓ
  /-- Makes `Level.param n`. -/
  mkLevelParam : Name → m ℓ
  /-- Makes `Level.mvar mvarId`. -/
  mkLevelMVar : LMVarId → m ℓ

export MonadMkLevel
  (mkLevelZero mkLevelMax mkLevelIPos mkLevelParam mkLevelMVar mkLevelOffset)

instance (ℓ m n) [MonadLift m n] [MonadGetLevel m ℓ] : MonadGetLevel n ℓ where
  getLevel u := liftM (getLevel u : m _)
  levelHash u := liftM (levelHash u : m _)

instance (ℓ m n) [MonadLift m n] [MonadMkLevel m ℓ] : MonadMkLevel n ℓ where
  mkLevelZero := liftM (mkLevelZero : m _)
  mkLevelOffset u n := liftM (mkLevelOffset u n : m _)
  mkLevelMax u v := liftM (mkLevelMax u v : m _)
  mkLevelIPos u v := liftM (mkLevelIPos u v : m _)
  mkLevelParam n := liftM (mkLevelParam n : m _)
  mkLevelMVar mvarId := liftM (mkLevelMVar mvarId : m _)

end LilLean
