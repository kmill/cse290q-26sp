module
import LilLean.Level.Context
import LilLean.PP.Level

/-!
# Tests of level contexts
-/

open LilLean

open Lean (logInfo)

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
  logInfo m!"{(← getLevelContext).stats}"

def mkLevelExpr1 : M LevelId := do
  mkLevelIMax (← mkLevelSucc (← mkLevelParam `u)) <|
    ← mkLevelIMax (← mkLevelSucc (← mkLevelParam `v)) (← mkLevelParam `w)

/--
info: u = max (ipos (u + 1) (max (ipos (v + 1) w) w)) (ipos (v + 1) w) w
---
info: normalized: max (ipos (u + 1) w) (ipos (v + 1) w) w
---
info: LevelContext stats:
- 2 blocks (1 in free list)
- 1 regions
- 7 total level expressions
-/
#guard_msgs in
#eval runM do
  let u ← withNewLevelRegion fun _ => do
    let u ← mkLevelExpr1
    logInfo m!"u = {← ppLevel u}"
    let w ← mkLevelExpr1
    unless ← levelEq u w do throwError "level eq fail"
    let v ← u.normalize
    withSetCurrLevelRegion LevelRegionId.static do
      promoteLevel v
  logInfo m!"normalized: {← ppLevel u}"
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
- 7 total level expressions
-/
#guard_msgs in
#eval runM do
  let u ← mkLevelExpr2 0
  logInfo m!"u = {← ppLevel u}, normalized = {← ppLevel (← u.normalize)}"
  let u ← mkLevelExpr2 2
  logInfo m!"u = {← ppLevel u}, normalized = {← ppLevel (← u.normalize)}"
  let u ← mkLevelExpr2 4
  logInfo m!"u = {← ppLevel u}, normalized = {← ppLevel (← u.normalize)}"
  logStats

/--
info: u = max 2 (u + 3), normalized = u + 3
---
info: LevelContext stats:
- 2 blocks (0 in free list)
- 2 regions
- 2 total level expressions
---
info: LevelContext stats:
- 2 blocks (1 in free list)
- 1 regions
- 0 total level expressions
-/
#guard_msgs in
#eval runM do
  withNewLevelRegion fun _ => do
    let u ← mkLevelExpr2 2
    logInfo m!"u = {← ppLevel u}, normalized = {← ppLevel (← u.normalize)}"
    logStats
  logStats

/--
info: u = max u 1; v = u + 1
---
info: u == v: false; u = v: false
---
info: u ≤ v: true; v ≤ u: false
---
info: max u v: u + 1
---
info: max u v: u + 1
-/
#guard_msgs in
#eval runM do
  withNewLevelRegion fun _ => do
    let u ← mkLevelMax (← mkLevelParam `u) (← mkLevelConst 1)
    let v ← mkLevelSucc (← mkLevelParam `u)
    logInfo m!"u = {← ppLevel u}; v = {← ppLevel v}"
    logInfo m!"u == v: {u == v}; u = v: {← levelEq u v}"
    logInfo m!"u ≤ v: {← levelLE u v}; v ≤ u: {← levelLE v u}"
    logInfo m!"max u v: {(← ppLevel (← (← mkLevelMax u v).normalize))}"
    logInfo m!"max u v: {(← ppLevel (← (← mkLevelIMax u v).normalize))}"

/--
info: x = max u v; y = max (ipos u v) v
---
info: x = y: false, x ≤ y: false, x ≥ y: true
---
info: x = max (u + 1) (v + 1); y = max (ipos (u + 1) v) (v + 1)
---
info: x = y: false, x ≤ y: false, x ≥ y: true
-/
#guard_msgs in
#eval runM do
  withNewLevelRegion fun _ => do
    let x ← mkLevelMax (← mkLevelParam `u) (← mkLevelParam `v)
    let y ← mkLevelIMax (← mkLevelParam `u) (← mkLevelParam `v)
    logInfo m!"x = {← ppLevel x}; y = {← ppLevel y}"
    logInfo m!"x = y: {← levelEq x y}, x ≤ y: {← levelLE x y}, x ≥ y: {← levelLE y x}"
    let x ← (← mkLevelSucc x).normalize
    let y ← (← mkLevelSucc y).normalize
    logInfo m!"x = {← ppLevel x}; y = {← ppLevel y}"
    logInfo m!"x = y: {← levelEq x y}, x ≤ y: {← levelLE x y}, x ≥ y: {← levelLE y x}"
