/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Declaration

/-!
# Global environment

This module defines the global environment object.
-/

public section

namespace LilLean

structure Environment where
  /-- The constructor. Private to avoid disallowed modification. -/
  private mk ::
  /-- The persistent hash map of global constants in the environment. -/
  constants : Lean.PersistentHashMap Name Declaration
  -- todo: environment extensions

class MonadEnv (m : Type → Type) where
  getEnv    : m Environment
  modifyEnv : (Environment → Environment) → m Unit

export MonadEnv (getEnv modifyEnv)

end LilLean
