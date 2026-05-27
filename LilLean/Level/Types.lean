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
Unique identifier for universe level metavariables.
-/
structure LMVarId where
  id : Nat
  deriving Inhabited, DecidableEq, Hashable, Repr, Ord

/--
Universe level. The type is non-recursive, and recursion is represented
indirectly through the `u` type, which represents a handle to a `Level`.

Note: One can make a recursive version of this type using
```
structure Level' where
  level : Level Level'
```
-/
inductive Level (ℓ : Type) where
  | zero  : Level ℓ
  | succ  : ℓ → Level ℓ
  | max   : ℓ → ℓ → Level ℓ
  /-- `ipos u v` means `if v = 0 then 0 else u`.
  This is used to implement impredicativity of `Prop`:
  given `α : Sort u` and `β : Sort v`,
  then `α → β : Sort (max (ipos u v) v)`.
  (In Lean 4, instead it's `α → β : imax u v`. The intent of `ipos` is to have
  more flexible algebraic rules for universe level normalization.) -/
  | ipos  : ℓ → ℓ → Level ℓ
  | param : Name → Level ℓ
  | mvar  : LMVarId → Level ℓ
  deriving Inhabited

/--
Monad for traversing level expressions.
The handle type `ℓ` is determined by the monad `m`.
-/
class MonadGetLevel (m : Type → Type) (ℓ : outParam Type) where
  /-- Gets the level referred to by the handle `ℓ`. -/
  getLevel (u : ℓ) : m (Level ℓ)
  /-- Follows the `Level.succ` chain and returns how many `succ`s there were. -/
  getLevelOffset (u : ℓ) : m (ℓ × Nat)
  /-- Returns whether or not the level contains a metavariable.
  (Note: metavariables might be assigned with respect to the current
  metavariable context.) -/
  levelHasMVar (u : ℓ) : m Bool
  /-- Returns whether or not the level contains a parameter. -/
  levelHasParam (u : ℓ) : m Bool
  /-- Returns a hash of the level.
  Lowest two bits encode hasParam (bit 0) and hasMVar (bit 1). -/
  levelHash (u : ℓ) : m UInt64

export MonadGetLevel (getLevel getLevelOffset levelHasMVar levelHasParam levelHash)

/--
Monad for constructing level expressions.
The handle type `ℓ` is determined by the monad `m`.
-/
class MonadMkLevel (m : Type → Type) (ℓ : outParam Type) where
  /-- Makes `Level.zero`. -/
  mkLevelZero : m ℓ
  /-- Makes `Level.succ u`. -/
  mkLevelSucc : ℓ → m ℓ
  /-- Makes `Level.max u v`. -/
  mkLevelMax : ℓ → ℓ → m ℓ
  /-- Makes `Level.ipos u v`. This represents `if v = 0 then 0 else u`. -/
  mkLevelIPos : ℓ → ℓ → m ℓ
  /-- Makes `Level.param n`. -/
  mkLevelParam : Name → m ℓ
  /-- Makes `Level.mvar mvarId`. -/
  mkLevelMVar : LMVarId → m ℓ
  /-- `mkLevelOffset u n` applies `mkLevelSucc` to `u` `n` times. -/
  mkLevelOffset : ℓ → Nat → m ℓ

export MonadMkLevel
  (mkLevelZero mkLevelSucc mkLevelMax mkLevelIPos mkLevelParam mkLevelMVar
    mkLevelOffset)

end LilLean
