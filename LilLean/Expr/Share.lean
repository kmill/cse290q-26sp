/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Level.Share
public import LilLean.Expr.Basic

/-!
# Common expression sharing

This module provides a system for sharing common subexpressions ("hash-consing")
for expressions.
-/

public section

namespace LilLean

local instance {ℓ} [BEq ℓ] : BEq (Level ℓ) :=
  ⟨Level.eq⟩
local instance {ℓ ε} [BEq ℓ] [BEq ε] : BEq (Expr ℓ ε) :=
  ⟨Expr.eq (alpha := false)⟩

structure ShareExpr (ℓ ε : Type) [BEq ℓ] [Hashable ℓ] [BEq ε] [Hashable ε]
    extends ShareLevel ℓ where
  exprs : Std.HashMap (Expr ℓ ε) ε := {}

variable {ℓ ε : Type} [BEq ℓ] [Hashable ℓ] [BEq ε] [Hashable ε]
variable {m : Type → Type} [Monad m] [MonadGetExpr m ℓ ε] [MonadMkExpr m ℓ ε]

partial def ShareExpr.shareLevelAux (u : ℓ) :
    StateT (ShareExpr ℓ ε) m ℓ := do
  let levelState ← modifyGet fun s =>
    (s.toShareLevel, { s with toShareLevel := {} })
  let (u, levelState) ← ShareLevel.shareAux u |>.run levelState
  modify fun s => { s with toShareLevel := levelState }
  return u

partial def ShareExpr.shareAux (e : ε) :
    StateT (ShareExpr ℓ ε) m ε := do
  let e' ← getExpr e
  if let some e := (← get).exprs[e']? then
    return e
  else
    let e ← exprMapDepthM
      ShareExpr.shareLevelAux
      (fun a _ => shareAux a)
      e 0
    modify fun s => { s with exprs := s.exprs.insert e' e }
    return e

partial def ShareExpr.share (state : ShareExpr ℓ ε) (e : ε) :
    m (ε × ShareExpr ℓ ε) := do
  ShareExpr.shareAux e |>.run state

partial def ShareExpr.shareLevel (state : ShareExpr ℓ ε) (u : ℓ) :
    m (ℓ × ShareExpr ℓ ε) := do
  ShareExpr.shareLevelAux u |>.run state

end LilLean
