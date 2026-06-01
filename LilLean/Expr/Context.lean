/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Level.Context
public import LilLean.Expr.Basic

/-!
# Expression context

This module defines an *expression context*, which is a memory manager for
expressions. See `LilLean.Level.Context` for some discussion.

The expression context contains a level context.
-/

public section

namespace LilLean

/--
Handle for an `Expr` managed by a `ExprContext`.
-/
structure ExprId where private mk ::
  /--
  Bits 0-23: UInt24 block ID
  Bits 24-32: UInt9 index into the block
  Bits 48-63: UInt16 generation counter (to try to detect use-after-free bugs)

  If the block id is -1, then bits 24-43 denote the index for `Expr.bvar`
  -/
  idx : UInt64
  deriving BEq

instance : Hashable ExprId where
  hash := private ExprId.idx

private def exprIdBlockMask : UInt64 := ((1 <<< 24) - 1).toUInt64

def ExprId.bvar0 : ExprId :=
  { idx := exprIdBlockMask }

instance : Inhabited ExprId := ⟨ExprId.bvar0⟩

def ExprId.bvar (idx : Nat) : ExprId :=
  assert! idx + 1 < (1 <<< 20)
  { idx := exprIdBlockMask ||| (idx.toUInt64 <<< 24) }

/--
ID for a memory block in the `ExprContext`.
-/
private structure ExprBlockId where
  id : Nat
  deriving Inhabited

/--
ID for a region in the `ExprContext`.
-/
structure ExprRegionId where private mk ::
  /-- Unique id -/
  private uid : Nat
  /-- Index into the `ExprContext.regions` array -/
  private idx : Nat
  deriving Inhabited

instance : Ord ExprRegionId where
  compare := private fun r1 r2 => compare r1.uid r2.uid

private inductive ExprIdView where
  | bvar (idx : Nat)
  | handle (blockId : ExprBlockId) (idx : Nat) (generation : UInt16)

@[inline]
private def ExprId.view (u : ExprId) : ExprIdView :=
  if u.idx &&& exprIdBlockMask == exprIdBlockMask then
    ExprIdView.bvar (u.idx >>> 24).toNat
  else
    let blockId : ExprBlockId := { id := (u.idx &&& exprIdBlockMask).toNat }
    let idx := ((u.idx >>> 24) &&& 511).toNat
    let generation := (u.idx >>> 48).toUInt16
    ExprIdView.handle blockId idx generation

private instance : ToString ExprIdView where
  toString
    | .bvar idx => s!"(bvar {idx})"
    | .handle blockId idx generation =>
      s!"(handle {blockId.id}[{idx}] @ {generation})"

instance : ToString ExprId where
  toString u := private toString u.view

@[inline]
private def ExprIdView.toExprId : ExprIdView → ExprId
  | .bvar idx =>
    assert! idx + 1 < (1 <<< 20)
    { idx := (idx.toUInt64 <<< 24) ||| exprIdBlockMask }
  | .handle blockId idx generation =>
    assert! blockId.id < (1 <<< 24)
    { idx :=
      blockId.id.toUInt64
      ||| (idx.toUInt64 <<< 24)
      ||| (generation.toUInt64 <<< 48) }

private structure ExprBlock where
  /-- Region the block is associated to. -/
  regionId : ExprRegionId
  /-- Generation counter for the block. Incremented every time it is freed. -/
  generation : UInt16
  /-- Index to the first free slot in `exprs`. -/
  freeIdx : Nat
  /-- Uses an `Array` for the block. Assumption: these are rarely copied. -/
  exprs : Array (Expr LevelId ExprId)
  /-- Cache of hashes of corresponding expressions. -/
  hashes : Array UInt64

/-- Returns true if the block has free space. -/
private def ExprBlock.hasFree (block : ExprBlock) : Bool :=
  block.freeIdx < 512

private structure ExprRegion where
  regionId : ExprRegionId
  /-- Blocks owned by this region. The first block in the list is the one
  that is currently used for new allocations. -/
  blockIds : List ExprBlockId
  /-- The level region that levels should be allocated into for this region.
  Invariant: This expression region may have handles into `levelRegionId`` or
  older, not newer. Invariant: level regions from older to newer expression
  regions must be nondecreasing. -/
  levelRegionId : LevelRegionId
  /-- Forwarding pointers, for promoting expressions to older regions.
  See `promoteExpr`. -/
  forward : Std.HashMap ExprId ExprId := {}
  deriving Inhabited

/--
Context for allocating expressions.
-/
structure ExprContext where private mk ::
  /-- Array of all blocks, both those used by regions, and those in the
  `freeBlocks` list. -/
  private blocks : Lean.PersistentArray ExprBlock
  /-- Array of all allocation regions. -/
  private regions : Lean.PersistentArray ExprRegion
  /-- List of blocks in `blocks` that are free. -/
  private freeBlocks : List ExprBlockId
  levelContext : LevelContext
  nextRegionUId : Nat := 1
  /-- The current allocation region. Can be modified to change where
  expressions are being allocated. -/
  currRegionId : ExprRegionId

def ExprRegionId.static : ExprRegionId := { uid := 0, idx := 0 }

private def ExprBlock.init : ExprBlock where
  regionId := .static
  generation := 0
  freeIdx := 0
  exprs := Array.replicate 512 (.bvar 0)
  hashes := Array.replicate 512 0

private instance : Inhabited ExprBlock := ⟨.init⟩

/--
Creates the initial level context with a single allocation region.
-/
def ExprContext.init : ExprContext where
  blocks := List.toPArray' [ExprBlock.init]
  regions :=
    List.toPArray' [{
      regionId := .static,
      blockIds := [{ id := 0}],
      levelRegionId := .static }]
  freeBlocks := []
  levelContext := .init
  currRegionId := .static

instance : Inhabited ExprContext := ⟨.init⟩

private def ExprContext.getBlock (ctx : ExprContext) (bid : ExprBlockId) :
    ExprBlock :=
  ctx.blocks.get! bid.id

private def ExprContext.modifyBlock (ctx : ExprContext) (bid : ExprBlockId)
    (f : ExprBlock → ExprBlock) : ExprContext :=
  { ctx with blocks := ctx.blocks.modify bid.id f }

private def ExprContext.getRegion (ctx : ExprContext) (rid : ExprRegionId) :
    ExprRegion :=
  let region := ctx.regions.get! rid.idx
  assert! region.regionId.uid == rid.uid
  region

private def ExprContext.modifyRegion (ctx : ExprContext) (rid : ExprRegionId)
    (f : ExprRegion → ExprRegion) : ExprContext :=
  { ctx with regions := ctx.regions.modify rid.idx f }

def ExprContext.getRegionId (ctx : ExprContext) (u : ExprId) :
    ExprRegionId :=
  match u.view with
  | .bvar .. => .static
  | .handle blockId .. => (ctx.getBlock blockId).regionId

def ExprContext.get (ctx : ExprContext) (u : ExprId) : Expr LevelId ExprId :=
  match u.view with
  | .bvar idx => Expr.bvar idx
  | .handle blockId idx generation =>
    let block := ctx.getBlock blockId
    assert! block.generation == generation
    block.exprs[idx]!

def ExprContext.getHash (ctx : ExprContext) (u : ExprId) : UInt64 :=
  match u.view with
  | .bvar idx => Expr.hashBVar idx
  | .handle blockId idx generation =>
    let block := ctx.getBlock blockId
    assert! block.generation == generation
    block.hashes[idx]!

/-- Gets the block that the region is allocating into. -/
private def ExprContext.regionCurrBlockId (ctx : ExprContext)
    (rid : ExprRegionId) : ExprBlockId :=
  (ctx.getRegion rid).blockIds.head!

/-- Resets the free index and increments the generation counter. -/
private def ExprBlock.reset (b : ExprBlock) : ExprBlock :=
  { b with freeIdx := 0, generation := b.generation + 1 }

/-- Allocates a new block, possibly by drawing it from the free list. -/
private def ExprContext.newBlock (ctx : ExprContext) :
    ExprBlockId × ExprContext :=
  match ctx.freeBlocks with
  | freeBlock :: freeBlocks =>
    (freeBlock, { ctx with freeBlocks })
  | [] =>
    let block := ExprBlock.init
    let blockId : ExprBlockId := { id := ctx.blocks.size }
    (blockId, { ctx with blocks := ctx.blocks.push block })

/--
Adds the block to the free list. Increments the generation counter to invalidate
any existing handles.
-/
private def ExprContext.freeBlock (ctx : ExprContext) (bid : ExprBlockId) :
    ExprContext :=
  { ctx.modifyBlock bid ExprBlock.reset with
    freeBlocks := bid :: ctx.freeBlocks }

/-- Allocates a new block for a region. -/
private def ExprContext.regionNewBlock (ctx : ExprContext)
    (rid : ExprRegionId) : ExprBlockId × ExprContext :=
  let (blockId, ctx) := ctx.newBlock
  let ctx := ctx.modifyBlock blockId fun block => { block with regionId := rid }
  let ctx := ctx.modifyRegion rid fun region =>
    { region with blockIds := blockId :: region.blockIds }
  (blockId, ctx)

private def ExprContext.newRegionId (ctx : ExprContext) :
    ExprRegionId × ExprContext :=
  let uid := ctx.nextRegionUId
  ({ uid, idx := ctx.regions.size }, { ctx with nextRegionUId := uid + 1 })

/--
Creates a new allocation region. By default, new allocations go into this
region. Captures the curent level region.
-/
def ExprContext.pushRegion (ctx : ExprContext) :
    ExprRegionId × ExprContext :=
  let (regionId, ctx) := ctx.newRegionId
  let (bid, ctx) := ctx.newBlock
  let ctx := ctx.modifyBlock bid fun block => { block with regionId }
  let levelRegionId := ctx.levelContext.currRegionId
  assert! (compare (ctx.getRegion ctx.currRegionId).levelRegionId levelRegionId).isLE
  let ctx := { ctx with
    regions := ctx.regions.push { regionId, blockIds := [bid], levelRegionId } }
  (regionId, ctx)

/--
Deallocates the last region that was created with `pushRegion`.
All handles to levels contained within it become invalid.
The region id must be the region being deallocated.
-/
def ExprContext.popRegion (ctx : ExprContext)
    (rid : ExprRegionId) :
    ExprContext :=
  assert! ctx.regions.size > 1 -- cannot free static region
  assert! (compare ctx.currRegionId rid).isLT -- ensure curr still will be valid
  let r := ctx.regions.get! (ctx.regions.size - 1)
  assert! (compare r.regionId rid).isEq
  let ctx := { ctx with regions := ctx.regions.pop }
  let ctx := r.blockIds.foldl (init := ctx) freeBlock
  ctx

/--
Returns the current allocation block for the region, allocating a new
block if the current one is full.
-/
private def ExprContext.regionAllocBlockId (ctx : ExprContext)
    (rid : ExprRegionId) : ExprBlockId × ExprContext :=
  let blockId := ctx.regionCurrBlockId rid
  if (ctx.getBlock blockId).hasFree then
    (blockId, ctx)
  else
    ctx.regionNewBlock rid

/-- Allocates an expression in the given region. -/
def ExprContext.regionMkExpr (ctx : ExprContext) (rid : ExprRegionId)
    (e : Expr LevelId ExprId) : ExprId × ExprContext :=
  if let .bvar idx := e then
    (ExprId.bvar idx, ctx)
  else
    let hash := e.hashCore ctx.levelContext.getHash ctx.getHash
    let (blockId, ctx) := ctx.regionAllocBlockId rid
    let block := ctx.getBlock blockId
    assert! block.hasFree
    let { freeIdx := idx, generation, .. } := block
    let ctx := ctx.modifyBlock blockId fun block =>
      { block with
        freeIdx := block.freeIdx + 1
        exprs := block.exprs.set! idx e
        hashes := block.hashes.set! idx hash }
    ((ExprIdView.handle blockId idx generation).toExprId, ctx)

/-- Allocates an expression in the current region. -/
def ExprContext.mkExpr (ctx : ExprContext)
    (e : Expr LevelId ExprId) : ExprId × ExprContext :=
  ctx.regionMkExpr ctx.currRegionId e

def ExprContext.modifyGetLevelContext {α : Type}
    (f : LevelContext → α × LevelContext) (ctx : ExprContext) :
    α × ExprContext :=
  let (x, levelContext) := f ctx.levelContext
  (x, { ctx with levelContext })

def ExprContext.stats (ctx : ExprContext) : String :=
  let totalLevels := ctx.blocks.foldl (init := 0) fun total block =>
    total + block.freeIdx
  s!"ExprContext stats:\n\
  - {ctx.blocks.size} blocks ({ctx.freeBlocks.length} in free list)\n\
  - {ctx.regions.size} regions\n\
  - {totalLevels} total expressions\n{ctx.levelContext.stats}"

@[inline] def ExprContext.exprGetter (ctx : ExprContext) :
    ExprGetter LevelId ExprId where
  level := ctx.levelContext.levelGetter
  getExpr := ctx.get
  exprHash := ctx.getHash

/--
Class for monads that contain `ExprContext` state.
This provides `MonadGetLevel` and `MonadMkLevel` instances.
-/
class MonadExprContext (m : Type → Type) where
  getExprContext : m ExprContext
  modifyGetExprContext {α} (f : ExprContext → α × ExprContext) : m α

@[inline]
def MonadExprContext.modifyExprContext {m : Type → Type} [MonadExprContext m]
    (f : ExprContext → ExprContext) : m Unit :=
  modifyGetExprContext fun ctx => ((), f ctx)

export MonadExprContext (getExprContext modifyGetExprContext modifyExprContext)

instance (m : Type → Type) [Monad m] [MonadExprContext m] :
    MonadLevelContext m where
  getLevelContext := ExprContext.levelContext <$> getExprContext
  modifyGetLevelContext f :=
    modifyGetExprContext (ExprContext.modifyGetLevelContext f)

instance (m : Type → Type) [Monad m] [MonadExprContext m] :
    MonadGetExpr m LevelId ExprId where
  getExprGetter := ExprContext.exprGetter <$> getExprContext

instance (m : Type → Type) [Monad m] [MonadExprContext m] :
    MonadMkExpr m LevelId ExprId where
  mkExpr e := modifyGetExprContext (fun ctx => ctx.mkExpr e)

namespace ExprId
variable {m : Type → Type} [Monad m] [MonadExprContext m]

def get (e : ExprId) : m (Expr LevelId ExprId) :=
  getExpr e

def hasLevelMVar (e : ExprId) : m Bool :=
  exprHasLevelMVar e

def hasExprMVar (e : ExprId) : m Bool :=
  exprHasExprMVar e

def hasMVar (e : ExprId) : m Bool :=
  exprHasMVar e

def hasLevelParam (e : ExprId) : m Bool :=
  exprHasLevelParam e

def hasFVar (e : ExprId) : m Bool :=
  exprHasFVar e

def looseBVarRange (e : ExprId) : m Nat :=
  exprLooseBVarRange e

def hasLooseBVars (e : ExprId) : m Bool :=
  exprHasLooseBVars e

def hash (e : ExprId) : m UInt64 :=
  exprHash e

/--
Structural equality.
-/
def eq (e e' : ExprId) (alpha := false) : m Bool :=
  exprEq e e' (alpha := alpha)

/--
Structural equality, ignoring binder names and binder info.
-/
def equiv (e e' : ExprId) : m Bool :=
  exprEquiv e e'

end ExprId

/-- Monad for doing `ExprContext` manipulations. -/
abbrev ExprContext.M := StateM ExprContext

instance : MonadExprContext ExprContext.M where
  getExprContext := get
  modifyGetExprContext := modifyGet

instance : MonadLift LevelContext.M ExprContext.M where
  monadLift x := modifyGetLevelContext x.run

section Promote

partial def promoteExprCore (e : ExprId) : ExprContext.M ExprId := do
  match e.view with
  | .bvar .. => return e
  | .handle blockId _ generation =>
    let ctx ← getExprContext
    let block := ctx.getBlock blockId
    assert! block.generation == generation
    let rid := block.regionId
    if (compare rid ctx.currRegionId).isLE then
      return e
    else
      if let some e' := (ctx.getRegion rid).forward[e]? then
        promoteExprCore e'
      else
        let e' ← mkExpr =<< (← e.get).mapM (promoteLevelCore ·) promoteExprCore
        modifyExprContext fun ctx => ctx.modifyRegion rid fun region =>
          { region with forward := region.forward.insert e e' }
        return e'

/--
If `e` is in a newer region than the current region, copies it into the current
region, returning the copied expression.

This is intended to be used with `withSetCurrExprRegion`, and it is like a
tracing garbage collection step before returning from `withNewExprRegion`.
-/
partial def promoteExpr {m : Type → Type} [MonadExprContext m]
    (e : ExprId) : m ExprId :=
  modifyGetExprContext <| (promoteExprCore e).run

end Promote

section MonadExprContext
variable {m : Type → Type} [Monad m] [MonadExprContext m]

/--
Temporarily sets the current expr allocation region while executing `x`.
This also sets the current level allocation region to the one associated
to `regionId`.
-/
def withSetCurrExprRegion [MonadFinally m] {α}
    (regionId : ExprRegionId) (x : m α) : m α := do
  let levelRegionId := ((← getExprContext).getRegion regionId).levelRegionId
  let oldRegionId ← modifyGetExprContext (fun ctx =>
    (ctx.currRegionId, { ctx with currRegionId := regionId }))
  try
    withSetCurrLevelRegion levelRegionId x
  finally
    modifyExprContext (fun ctx => { ctx with currRegionId := oldRegionId })

/--
Runs `f` with a new expression allocation region, deallocating the region at
the end. Uses the current level region.
-/
def withNewExprRegion [MonadFinally m] {α}
    (f : ExprRegionId → m α) : m α := do
  let rid ← modifyGetExprContext (fun ctx => ctx.pushRegion)
  try
    withSetCurrExprRegion rid do f rid
  finally
    modifyExprContext (fun ctx => ctx.popRegion rid)

/--
Runs `f` with a new expression and level allocation regions, deallocating the
regions at the end. The level region ID is
-/
def withNewLevelExprRegions [MonadFinally m] {α}
    (f : LevelRegionId → ExprRegionId → m α) : m α := do
  withNewLevelRegion fun lrid => do
    withNewExprRegion fun erid => do
      f lrid erid

end MonadExprContext

end LilLean
