/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Level.Context
public import LilLean.Expr.Types

/-!
# Expression context

This module defines an *expression context*, which is a memory manager for
expressions. See `LilLean.Level.Context` for some discussion.
-/

public section

namespace LilLean

/--
In an expression handle, the lower bits are an index into a block, and the
higher bits are an index for the block itself.
-/
private def exprContextBlockSizeBits : Nat := 8

private def exprContextBlockSize : Nat :=
  1 <<< exprContextBlockSizeBits

/--
Handle for `Expr` expressions, for use with `ExprContext`.
-/
structure ExprId where
  /-- Index for the expression. Lowest `exprContextBlockSizeBits` bits are an
  index into a block, and the higher bits are the block index. Block `0` is
  reserved to represent small `Expr.bvar`s. -/
  idx : UInt32
  /-- A generation counter for detecting use-after-free bugs. Block IDs are
  reused, but their generation is bumped up. This counter will wrap around after
  long periods of operation, so false negatives are possible. -/
  generation : UInt16
  deriving DecidableEq

def ExprId.bvar (idx : Nat) : ExprId where
  idx :=
    if idx < exprContextBlockSize then idx.toUInt32
    else panic!"bvar index too large"
  generation := 0

instance : Inhabited ExprId := ⟨.bvar 0⟩

structure ExprBlockId where
  id : Nat
  deriving Inhabited

structure ExprRegionId where
  id : Nat
  deriving Inhabited

structure ExprBlock where
  /-- Region the block is associated to. -/
  region : ExprRegionId
  generation : UInt16
  freeIdx : UInt16
  /-- Uses an `Array` for the block. Assumption: these are rarely copied. -/
  exprs : Array (Expr LevelId ExprId)
  /-- Records hashes, as well as the `hasMVar` and `hasParam` bits. -/
  hashes : Array UInt64

structure ExprRegion where
  /-- Blocks owned by this region. The first block in the list is the one
  that is currently used for new allocations. -/
  blockIds : List ExprBlockId
  deriving Inhabited

/--
Context for allocating `Level` expressions.
-/
structure ExprContext where
  /-- Array of all blocks, both those used by regions, and those in the
  `freeBlocks` list. -/
  blocks : Lean.PersistentArray ExprBlock
  /-- Array of all allocation regions. -/
  regions : Lean.PersistentArray ExprRegion
  /-- List of blocks in `blocks` that are free. -/
  freeBlocks : List ExprBlockId
  levelContext : LevelContext

def ExprBlock.init : ExprBlock where
  region := { id := 0 }
  generation := 0
  freeIdx := 0
  exprs := Array.replicate exprContextBlockSize default
  hashes := Array.replicate exprContextBlockSize 0

instance : Inhabited ExprBlock := ⟨.init⟩

/--
Creates the initial level context, reserving block 0 for `Expr.bvar`.
-/
def ExprContext.init : ExprContext where
  blocks := List.toPArray' [ExprBlock.init, ExprBlock.init]
  regions := List.toPArray' [{ blockIds := [{ id := 1 }, { id := 0 }] }]
  freeBlocks := []
  levelContext := LevelContext.init

instance : Inhabited ExprContext := ⟨.init⟩

def ExprContext.getBlock (ctx : ExprContext) (bid : ExprBlockId) :
    ExprBlock :=
  ctx.blocks.get! bid.id

def ExprContext.modifyBlock (ctx : ExprContext) (bid : ExprBlockId)
    (f : ExprBlock → ExprBlock) : ExprContext :=
  { ctx with blocks := ctx.blocks.modify bid.id f }

def ExprContext.getRegion (ctx : ExprContext) (rid : ExprRegionId) : ExprRegion :=
  ctx.regions.get! rid.id

def ExprContext.modifyRegion (ctx : ExprContext) (rid : ExprRegionId)
    (f : ExprRegion → ExprRegion) : ExprContext :=
  { ctx with regions := ctx.regions.modify rid.id f }

def ExprId.getBlockIdAndIndex (u : ExprId) :
    ExprBlockId × Nat :=
  let blockId := u.idx >>> exprContextBlockSizeBits.toUInt32
  let exprIdx := u.idx &&& (exprContextBlockSize.toUInt32 - 1)
  ({ id := blockId.toNat }, exprIdx.toNat)

def ExprId.mkIdx (blockId : ExprBlockId) (index : Nat) :=
  (blockId.id.toUInt32 <<< exprContextBlockSizeBits.toUInt32) ||| index.toUInt32

def ExprContext.getBlockAndIndex (ctx : ExprContext) (u : ExprId) :
    ExprBlock × Nat :=
  let (blockId, exprIdx) := u.getBlockIdAndIndex
  let block := ctx.getBlock blockId
  assert! block.generation == u.generation
  (block, exprIdx)

def ExprContext.getRegionId (ctx : ExprContext) (u : ExprId) :
    ExprRegionId :=
  (ctx.getBlockAndIndex u).1.region

def ExprContext.get (ctx : ExprContext) (u : ExprId) : Expr LevelId ExprId :=
  let (blockId, exprIdx) := u.getBlockIdAndIndex
  if blockId.id == 0 then
    Expr.bvar exprIdx
  else
    let (block, exprIdx) := ctx.getBlockAndIndex u
    block.exprs[exprIdx]!

def ExprContext.getHash (ctx : ExprContext) (u : ExprId) : UInt64 :=
  if u.idx == 0 then
    -- Special case: idx 0 is Level.zero
    Level.hashAddOffset 0 u.offset.toNat
  else
    let (block, idx) := ctx.getBlockAndIndex u
    Level.hashAddOffset block.hashes[idx]! u.offset.toNat

def ExprContext.hasParam (ctx : ExprContext) (u : ExprId) : Bool :=
  (ctx.getHash u) &&& 1 != 0

def ExprContext.hasMVar (ctx : ExprContext) (u : ExprId) : Bool :=
  (ctx.getHash u) &&& 2 != 0

/-- Gets the region at the top of the region stack. -/
def ExprContext.currRegionId (ctx : ExprContext) : ExprRegionId :=
  { id := ctx.regions.size - 1 }

/-- Gets the block that the region is allocating into. -/
def ExprContext.regionCurrBlockId (ctx : ExprContext)
    (rid : ExprRegionId) : ExprBlockId :=
  (ctx.getRegion rid).blockIds.head!

/-- Resets the free index and increments the generation counter. -/
def ExprBlock.reset (b : ExprBlock) : ExprBlock :=
  { b with freeIdx := 0, generation := b.generation + 1 }

/-- Allocates a new block, possibly by drawing it from the free list. -/
def ExprContext.mkBlock (ctx : ExprContext) : ExprBlockId × ExprContext :=
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
def ExprContext.freeBlock (ctx : ExprContext) (bid : ExprBlockId) :
    ExprContext :=
  { ctx.modifyBlock bid ExprBlock.reset with
    freeBlocks := bid :: ctx.freeBlocks }

/-- Allocates a new block for a region. -/
def ExprContext.regionMkBlock (ctx : ExprContext) (rid : ExprRegionId) :
    ExprBlockId × ExprContext :=
  let (blockId, ctx) := ctx.mkBlock
  let ctx := ctx.modifyBlock blockId fun block => { block with region := rid }
  let ctx := ctx.modifyRegion rid fun region =>
    { region with blockIds := blockId :: region.blockIds }
  (blockId, ctx)

/--
Creates a new allocation region. By default, new allocations go into this
region.
-/
def ExprContext.pushRegion (ctx : ExprContext) :
    ExprRegionId × ExprContext :=
  let rid : ExprRegionId := { id := ctx.regions.size }
  let (bid, ctx) := ctx.mkBlock
  let ctx := ctx.modifyBlock bid fun block => { block with region := rid }
  let ctx := { ctx with regions := ctx.regions.push { blockIds := [bid] } }
  (rid, ctx)

/--
Deallocates the last region that was created with `pushRegion`.
All handles to levels contained within it become invalid.
-/
def ExprContext.popRegion (ctx : ExprContext) : ExprContext :=
  assert! ctx.regions.size > 1
  let r := ctx.regions.get! (ctx.regions.size - 1)
  let ctx := { ctx with regions := ctx.regions.pop }
  let ctx := r.blockIds.foldl (init := ctx) freeBlock
  ctx

/-- Returns true if the block has free space. -/
def ExprBlock.hasFree (block : ExprBlock) : Bool :=
  block.freeIdx.toNat < exprContextBlockSize

/--
Returns the current allocation block for the region, allocating a new
block if the current one is full.
-/
def ExprContext.regionAllocBlockId (ctx : ExprContext)
    (rid : ExprRegionId) : ExprBlockId × ExprContext :=
  let blockId := ctx.regionCurrBlockId rid
  let block := ctx.getBlock blockId
  if block.hasFree then
    (blockId, ctx)
  else
    ctx.regionMkBlock rid

/-- Allocates a level in the given region. -/
def ExprContext.regionMkLevelOffset (ctx : ExprContext) (rid : ExprRegionId)
    (u : Level ExprId) (offset : Nat) : ExprId × ExprContext :=
  if let .succ u' := u then
    ({ u' with offset := mkOffset (offset + u'.offset.toNat + 1) }, ctx)
  else
    let hash := u.hashCore 0 ctx.getHash
    let (blockId, ctx) := ctx.regionAllocBlockId rid
    let block := ctx.getBlock blockId
    assert! block.hasFree
    let { freeIdx, generation, .. } := block
    let index := freeIdx.toNat
    let ctx := ctx.modifyBlock blockId fun block =>
      { block with
        freeIdx := block.freeIdx + 1
        levels := block.levels.set! index u
        hashes := block.hashes.set! index hash }
    let levelId : ExprId :=
      { idx := ExprId.mkIdx blockId index
        offset := mkOffset offset
        generation }
    (levelId, ctx)

/-- Allocates a level in the current region. -/
def ExprContext.mkLevelOffset (ctx : ExprContext)
    (u : Level ExprId) (offset : Nat) : ExprId × ExprContext :=
  let rid := ctx.currRegionId
  ctx.regionMkLevelOffset rid u offset

def ExprContext.mkMax (ctx : ExprContext) (u v : ExprId) :
    ExprId × ExprContext :=
  ctx.mkLevelOffset (Level.max u v) 0

def ExprContext.mkIPos (ctx : ExprContext) (u v : ExprId) :
    ExprId × ExprContext :=
  ctx.mkLevelOffset (Level.ipos u v) 0

def ExprContext.mkParam (ctx : ExprContext) (n : Name) :
    ExprId × ExprContext :=
  ctx.mkLevelOffset (Level.param n) 0

def ExprContext.mkMVar (ctx : ExprContext) (mvarId : LMVarId) :
    ExprId × ExprContext :=
  ctx.mkLevelOffset (Level.mvar mvarId) 0

def ExprContext.stats (ctx : ExprContext) : String :=
  let totalLevels := ctx.blocks.foldl (init := 0) fun total block =>
    total + block.freeIdx.toNat
  s!"ExprContext stats:\n\
  - {ctx.blocks.size} blocks ({ctx.freeBlocks.length} in free list)\n\
  - {ctx.regions.size} regions\n\
  - {totalLevels} level expressions"

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

instance (m : Type → Type) [Monad m] [MonadExprContext m] : MonadGetLevel m ExprId where
  getLevel u := (ExprContext.get · u) <$> getExprContext
  getLevelOffset u := pure u.getOffset
  levelHasMVar u := (ExprContext.hasMVar · u) <$> getExprContext
  levelHasParam u := (ExprContext.hasParam · u) <$> getExprContext
  levelHash u := (ExprContext.getHash · u) <$> getExprContext

instance (m : Type → Type) [Monad m] [MonadExprContext m] : MonadMkLevel m ExprId where
  mkLevelZero := pure ExprId.zero
  mkLevelSucc u := pure u.succ
  mkLevelMax u v := modifyGetExprContext (fun ctx => ctx.mkMax u v)
  mkLevelIPos u v := modifyGetExprContext (fun ctx => ctx.mkIPos u v)
  mkLevelParam n := modifyGetExprContext (fun ctx => ctx.mkParam n)
  mkLevelMVar mvarId := modifyGetExprContext (fun ctx => ctx.mkMVar mvarId)
  mkLevelOffset u offset := pure <| u.addOffset offset

namespace ExprId
variable {m : Type → Type} [Monad m] [MonadExprContext m]

def get (u : ExprId) : m (Level ExprId) :=
  getLevel u

def hasMVar (u : ExprId) : m Bool :=
  MonadGetLevel.levelHasMVar u

def hasParam (u : ExprId) : m Bool :=
  MonadGetLevel.levelHasParam u

def hash (u : ExprId) : m UInt64 :=
  MonadGetLevel.levelHash u

/--
Normalizes the level. Does not instantiate metavariables.
-/
def normalize (u : ExprId) : m ExprId :=
  normalizeLevel u

/--
Structural equality.
-/
def eq (u v : ExprId) : m Bool :=
  levelEq u v

/--
Level equivalence.
-/
def equiv (u v : ExprId) : m Bool :=
  levelEquiv u v

def le (u v : ExprId) : m Bool :=
  levelLE u v

end ExprId

section MonadExprContext
variable {m : Type → Type} [Monad m] [MonadExprContext m]

/--
Runs `f` with a new allocation region, deallocating the region at the end.
-/
def withNewExprRegion [MonadFinally m] {α}
    (f : ExprRegionId → m α) : m α := do
  let rid ← modifyGetExprContext (fun ctx => ctx.pushRegion)
  try
    f rid
  finally
    modifyExprContext (fun ctx => ctx.popRegion)

end MonadExprContext

end LilLean
