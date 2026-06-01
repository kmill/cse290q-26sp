/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Expr.Basic

/-!
# Collection of free variables in an expression
-/

public section

namespace LilLean

namespace CollectFVars

structure State (ℓ ε : Type) [BEq ε] [Hashable ε] where
  fvarIds : Array FVarId := #[]
  fvarIdSet : Std.HashSet FVarId := {}
  visited : Std.HashSet ε := {}

variable {ℓ ε : Type} [BEq ε] [Hashable ε] {ctx : ExprGetter ℓ ε}

partial def visit {alpha} (e : Expr' ctx alpha)
    (state : State ℓ ε) : State ℓ ε :=
  if !e.hasFVar || state.visited.contains e.handle then
    state
  else
    let state := { state with visited := state.visited.insert e.handle }
    match e.get with
    | .fvar fvarId =>
      if state.fvarIdSet.contains fvarId then
        state
      else
        { state with
          fvarIds := state.fvarIds.push fvarId,
          fvarIdSet := state.fvarIdSet.insert fvarId }
    | .bvar .. => state
    | .mvar .. => state
    | .sort .. => state
    | .const .. => state
    | .app fn arg => visit fn state |> visit arg
    | .lam _ t b _ => visit t state |> visit b
    | .pi _ t b _ => visit t state |> visit b
    | .let _ t v b => visit t state |> visit v |> visit b
    | .lit .. => state
    | .proj _ _ s => visit s state

end CollectFVars

variable {ℓ ε : Type} [BEq ε] [Hashable ε]

def ExprGetter.collectFVars (ctx : ExprGetter ℓ ε) (e : ε)
    (state : CollectFVars.State ℓ ε) : CollectFVars.State ℓ ε :=
  CollectFVars.visit (ctx.mkExpr' e) state

def collectFVars {m} [Monad m] [MonadGetExpr m ℓ ε] (e : ε)
    (state : CollectFVars.State ℓ ε) : m (CollectFVars.State ℓ ε) := do
  let ctx ← getExprGetter
  return CollectFVars.visit (ctx.mkExpr' e) state

end LilLean
