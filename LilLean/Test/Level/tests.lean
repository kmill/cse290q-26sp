module
import LilLean.Level.Context
import LilLean.PP.Level

/-!
# Tests of level contexts
-/

open LilLean

structure State where
  levelContext : LevelContext

abbrev M := StateRefT State Lean.CoreM
instance : MonadLevelContext M where
  getLevelContext := return (← get).levelContext
  modifyGetLevelContext f := modifyGet fun s =>
    let (v, levelContext) := f s.levelContext
    (v, { s with levelContext })

def runM {α} (m : M α) : Lean.CoreM α :=
  m.run' { levelContext := LevelContext.init }

def logStats : M Unit := do
  Lean.logInfo m!"{(← getLevelContext).stats}"

def mkLevelExpr1 : M LevelId := do
  mkLevelIMax (← mkLevelSucc (← mkLevelParam `u)) <|
    ← mkLevelIMax (← mkLevelSucc (← mkLevelParam `v)) (← mkLevelParam `w)

/--
info: u = max (ipos (u + 1) (max (ipos (v + 1) w) w)) (ipos (v + 1) w) w
---
info: normalized: max (ipos (u + 1) w) (ipos (v + 1) w) w
---
info: LevelContext stats:
- 1 blocks (0 in free list)
- 1 regions
- 12 level expressions
-/
#guard_msgs in
#eval runM do
  let u ← mkLevelExpr1
  Lean.logInfo m!"u = {← ppLevel u}"
  let u ← u.normalize
  Lean.logInfo m!"normalized: {← ppLevel u}"
  logStats

def mkLevelExpr2 (n : Nat) : M LevelId := do
  mkLevelMax (← mkLevelConst n) (← mkLevelOffset (← mkLevelParam `u) 3)

/--
info: u = max 0 (u + 3), normalized = u + 3
---
info: u = max 2 (u + 3), normalized = u + 3
---
info: u = max 4 (u + 3), normalized = max (u + 3) 4
---
info: LevelContext stats:
- 1 blocks (0 in free list)
- 1 regions
- 8 level expressions
-/
#guard_msgs in
#eval runM do
  let u ← mkLevelExpr2 0
  Lean.logInfo m!"u = {← ppLevel u}, normalized = {← ppLevel (← u.normalize)}"
  let u ← mkLevelExpr2 2
  Lean.logInfo m!"u = {← ppLevel u}, normalized = {← ppLevel (← u.normalize)}"
  let u ← mkLevelExpr2 4
  Lean.logInfo m!"u = {← ppLevel u}, normalized = {← ppLevel (← u.normalize)}"
  logStats
