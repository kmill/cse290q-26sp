/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Expr.Basic

/-!
# Collection of metavariables in an expression
-/

public section

namespace LilLean

namespace CollectMVars

structure State (ℓ ε : Type) [BEq ε] [Hashable ε] where
  mvarIds : Array MVarId := #[]
  mvarIdSet : Std.HashSet MVarId := {}
  visited : Std.HashSet ε := {}

variable {ℓ ε : Type} [BEq ε] [Hashable ε] {ctx : ExprGetter ℓ ε}

partial def visit {alpha} (e : Expr' ctx alpha)
    (state : State ℓ ε) : State ℓ ε :=
  if !e.hasExprMVar || state.visited.contains e.handle then
    state
  else
    let state := { state with visited := state.visited.insert e.handle }
    match e.get with
    | .mvar mvarId =>
      if state.mvarIdSet.contains mvarId then
        state
      else
        { state with
          mvarIds := state.mvarIds.push mvarId,
          mvarIdSet := state.mvarIdSet.insert mvarId }
    | .bvar .. => state
    | .fvar .. => state
    | .sort .. => state
    | .const .. => state
    | .app fn arg => visit fn state |> visit arg
    | .lam _ t b _ => visit t state |> visit b
    | .pi _ t b _ => visit t state |> visit b
    | .let _ t v b => visit t state |> visit v |> visit b
    | .lit .. => state
    | .proj _ _ s => visit s state

end CollectMVars

variable {ℓ ε : Type} [BEq ε] [Hashable ε]

def ExprGetter.collectMVars (ctx : ExprGetter ℓ ε) (e : ε)
    (state : CollectMVars.State ℓ ε) : CollectMVars.State ℓ ε :=
  CollectMVars.visit (ctx.mkExpr' e) state

def collectMVars {m} [Monad m] [MonadGetExpr m ℓ ε] (e : ε)
    (state : CollectMVars.State ℓ ε) : m (CollectMVars.State ℓ ε) := do
  let ctx ← getExprGetter
  return CollectMVars.visit (ctx.mkExpr' e) state

end LilLean
