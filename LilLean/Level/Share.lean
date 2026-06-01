/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Level.Basic

/-!
# Common expression sharing

This module provides a system for sharing common subexpressions ("hash-consing")
for level expressions.
-/

public section

namespace LilLean

local instance {ℓ} [BEq ℓ] : BEq (Level ℓ) := ⟨Level.eq⟩

structure ShareLevel (ℓ : Type) [BEq ℓ] [Hashable ℓ] where
  levels : Std.HashMap (Level ℓ) ℓ := {}

variable {ℓ : Type} [BEq ℓ] [Hashable ℓ]
variable {m : Type → Type} [Monad m] [MonadGetLevel m ℓ] [MonadMkLevel m ℓ]

partial def ShareLevel.shareAux (u : ℓ) :
    StateT (ShareLevel ℓ) m ℓ := do
  let u' ← getLevel u
  if let some v := (← get).levels[u']? then
    return v
  else
    let v ← levelMapM shareAux u
    modify fun s => { s with levels := s.levels.insert u' v }
    return v

partial def ShareLevel.share (state : ShareLevel ℓ) (u : ℓ) :
    m (ℓ × ShareLevel ℓ) := do
  ShareLevel.shareAux u |>.run state

end LilLean
