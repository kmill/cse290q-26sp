/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Level.Basic
public import LilLean.Parser.Level

/-!
# Level pretty printing
-/

public section

namespace LilLean

section
variable {m : Type → Type} {ℓ : Type} [Monad m] [MonadGetLevel m ℓ]
variable [Lean.MonadRef m] [Lean.MonadQuotation m]

partial def delabLevel (u : ℓ) : m (Lean.TSyntax `lilLevel) :=
  visit u
where
  visit (u : ℓ) : m (Lean.TSyntax `lilLevel) := do
    let (u', offset) ← getLevelOffset u
    let addOffset (stx : Lean.TSyntax `lilLevel) : m (Lean.TSyntax `lilLevel) :=
      if offset == 0 then
        return stx
      else
        `(lilLevel| $stx + $(Lean.quote offset):num)
    match (← getLevel u') with
    | .zero => `(lilLevel| $(Lean.quote offset):num)
    | .succ _ => unreachable!
    | .mvar mvarId =>
      -- Create a pseudo identifier for the level metavariable
      let s := Lean.mkIdent <| Lean.Name.mkSimple <| s!"?u.{mvarId.id+1}"
      `(lilLevel| $s:ident) >>= addOffset
    | .param n =>
      `(lilLevel| $(Lean.mkIdent n):ident) >>= addOffset
    | .max .. => visitMax u' #[] >>= addOffset
    | .ipos .. => visitIPos u' #[] >>= addOffset
  visitMax (u : ℓ) (acc : Array (Lean.TSyntax `lilLevel)) :
      m (Lean.TSyntax `lilLevel) := do
    match (← getLevel u) with
    | .max v w =>
      let acc := acc.push (← visit v)
      visitMax w acc
    | _ =>
      let acc := acc.push (← visit u)
      `(lilLevel| max $acc*)
  visitIPos (u : ℓ) (acc : Array (Lean.TSyntax `lilLevel)) :
      m (Lean.TSyntax `lilLevel) := do
    match (← getLevel u) with
    | .ipos v w =>
      let acc := acc.push (← visit v)
      visitIPos w acc
    | _ =>
      let acc := acc.push (← visit u)
      `(lilLevel| ipos $acc*)

def ppLevel [MonadLiftT Lean.CoreM m] (u : ℓ) : m Std.Format := do
  let stx ← delabLevel u
  let stx := (Lean.sanitizeSyntax stx).run' { options := {} }
  let stx ← Lean.PrettyPrinter.parenthesizeCategory `lilLevel stx
  Lean.PrettyPrinter.formatCategory `lilLevel stx

end

end LilLean
