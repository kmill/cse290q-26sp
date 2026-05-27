/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Level.Basic

/-!
# Level expression context

This module defines a *level context*, which is a memory manager for level
expressions. Recall that the `Level` type is non-recursive, using handles to
refer to levels, instead of using `Level` itself, which would require us to
design around Lean's memory manager and to use `@[computed_field]` and unsafe
pointer tricks.

To be low overhead, we use a region allocation scheme rather than reference
counting. Levels are allocated within blocks that are freed all at once. There
is a mechanism for maintaining a stack of regions, with the invariant
that older regions cannot point into newer regions; new levels can be allocated
into any region.

The handles record which block their memory is in. We also use the handle to
record constant offsets, saving the need to record `Level.succ`s in the blocks.

The level context is designed to be a persistent data structure, since we need
to be able to capture the level context for error reporting and logging
purposes.
-/

public section

namespace LilLean

/--
In a level handle, the lower bits are an index into a block, and the
higher bits are an index for the block itself.
-/
private def levelContextBlockSizeBits : Nat := 8

private def levelContextBlockSize : Nat :=
  1 <<< levelContextBlockSizeBits

/--
Handle for `Level` expressions, for use with `LevelContext`.
-/
structure LevelId where
  /-- Index for the level. Lowest `levelContextBlockSizeBits` bits are an index
  into a block, and the higher bits are the block index. Index `0` is reserved
  to represent `Level.zero`. -/
  idx : UInt32
  /-- Stores an offset representing a number of `Level.succ` constructors that
  are applied. This is an optimization to avoid needing to store long `succ`
  chains, and it also supports fast decrement. Constant levels (those
  that are successors of `Level.zero`) are represented entirely within a
  handle. Offsets greater than `2^16-1` are an error. -/
  offset : UInt16
  /-- A generation counter for detecting use-after-free bugs. Block IDs are
  reused, but their generation is bumped up. This counter will wrap around after
  long periods of operation, so false negatives are possible. -/
  generation : UInt16
  deriving DecidableEq

def LevelId.zero : LevelId where
  idx := 0
  offset := 0
  generation := 0

instance : Inhabited LevelId := ⟨.zero⟩

private def mkOffset (offset : Nat) : UInt16 :=
  if offset < (1 <<< 16) then
    offset.toUInt16
  else
    panic! "level offset exceeds 16 bits"

def LevelId.addOffset (u : LevelId) (offset : Nat) : LevelId :=
  { u with offset := mkOffset (u.offset.toNat + offset) }

def LevelId.succ (u : LevelId) : LevelId :=
  u.addOffset 1

structure LevelBlockId where
  id : Nat
  deriving Inhabited

structure LevelRegionId where
  id : Nat
  deriving Inhabited

structure LevelBlock where
  /-- Region the block is associated to. -/
  region : LevelRegionId
  generation : UInt16
  freeIdx : UInt16
  /-- Uses an `Array` for the block. Assumption: these are rarely copied. -/
  levels : Array (Level LevelId)
  /-- Records hashes, as well as the `hasMVar` and `hasParam` bits. -/
  hashes : Array UInt64

structure LevelRegion where
  /-- Blocks owned by this region. The first block in the list is the one
  that is currently used for new allocations. -/
  blockIds : List LevelBlockId
  -- /-- Cache of allocated parameters. -/
  -- params : Std.TreeMap Lean.Name LevelId Lean.Name.cmp
  -- /-- Cache of allocated metavariables. -/
  -- mvars : Std.TreeMap LMVarId LevelId
  deriving Inhabited

/--
Context for allocating `Level` expressions.
-/
structure LevelContext where
  /-- Array of all blocks, both those used by regions, and those in the
  `freeBlocks` list. -/
  blocks : Lean.PersistentArray LevelBlock
  /-- Array of all allocation regions. -/
  regions : Lean.PersistentArray LevelRegion
  /-- List of blocks in `blocks` that are free. -/
  freeBlocks : List LevelBlockId

def LevelBlock.init : LevelBlock where
  region := { id := 0 }
  generation := 0
  freeIdx := 0
  levels := Array.replicate levelContextBlockSize Level.zero
  hashes := Array.replicate levelContextBlockSize 0

instance : Inhabited LevelBlock := ⟨.init⟩

/--
Creates the initial level context, reserving idx 0 for `Level.zero`.
-/
def LevelContext.init : LevelContext where
  blocks :=
    -- Reserve first entry for `Level.zero`. Its hash is `0`.
    let initBlock := { LevelBlock.init with freeIdx := 1 }
    List.toPArray' [initBlock]
  regions := List.toPArray' [{ blockIds := [{ id := 0 }] }]
  freeBlocks := []

instance : Inhabited LevelContext := ⟨.init⟩

def LevelContext.getBlock (ctx : LevelContext) (bid : LevelBlockId) :
    LevelBlock :=
  ctx.blocks.get! bid.id

def LevelContext.modifyBlock (ctx : LevelContext) (bid : LevelBlockId)
    (f : LevelBlock → LevelBlock) : LevelContext :=
  { ctx with blocks := ctx.blocks.modify bid.id f }

def LevelContext.getRegion (ctx : LevelContext) (rid : LevelRegionId) : LevelRegion :=
  ctx.regions.get! rid.id

def LevelContext.modifyRegion (ctx : LevelContext) (rid : LevelRegionId)
    (f : LevelRegion → LevelRegion) : LevelContext :=
  { ctx with regions := ctx.regions.modify rid.id f }

def LevelId.getBlockIdAndIndex (u : LevelId) :
    LevelBlockId × Nat :=
  let blockId := u.idx >>> levelContextBlockSizeBits.toUInt32
  let levelIdx := u.idx &&& (levelContextBlockSize.toUInt32 - 1)
  ({ id := blockId.toNat }, levelIdx.toNat)

def LevelId.mkIdx (blockId : LevelBlockId) (index : Nat) :=
  (blockId.id.toUInt32 <<< levelContextBlockSizeBits.toUInt32) ||| index.toUInt32

def LevelContext.getBlockAndIndex (ctx : LevelContext) (u : LevelId) :
    LevelBlock × Nat :=
  let (blockId, levelIdx) := u.getBlockIdAndIndex
  let block := ctx.getBlock blockId
  assert! block.generation == u.generation
  (block, levelIdx)

def LevelContext.getRegionId (ctx : LevelContext) (u : LevelId) :
    LevelRegionId :=
  (ctx.getBlockAndIndex u).1.region

def LevelId.getOffset (u : LevelId) :
    LevelId × Nat :=
  if u.idx == 0 then
    -- Special case: idx 0 is Level.zero
    (LevelId.zero, u.offset.toNat)
  else
    ({ u with offset := 0 }, u.offset.toNat)

def LevelContext.get (ctx : LevelContext) (u : LevelId) : Level LevelId :=
  if u.offset > 0 then
    Level.succ { u with offset := u.offset - 1 }
  else if u.idx == 0 then
    Level.zero
  else
    let (block, index) := ctx.getBlockAndIndex u
    block.levels[index]!

def LevelContext.getHash (ctx : LevelContext) (u : LevelId) : UInt64 :=
  if u.idx == 0 then
    -- Special case: idx 0 is Level.zero
    Level.hashAddOffset 0 u.offset.toNat
  else
    let (block, idx) := ctx.getBlockAndIndex u
    Level.hashAddOffset block.hashes[idx]! u.offset.toNat

def LevelContext.hasParam (ctx : LevelContext) (u : LevelId) : Bool :=
  (ctx.getHash u) &&& 1 != 0

def LevelContext.hasMVar (ctx : LevelContext) (u : LevelId) : Bool :=
  (ctx.getHash u) &&& 2 != 0

/-- Gets the region at the top of the region stack. -/
def LevelContext.currRegionId (ctx : LevelContext) : LevelRegionId :=
  { id := ctx.regions.size - 1 }

/-- Gets the block that the region is allocating into. -/
def LevelContext.regionCurrBlockId (ctx : LevelContext)
    (rid : LevelRegionId) : LevelBlockId :=
  (ctx.getRegion rid).blockIds.head!

/-- Resets the free index and increments the generation counter. -/
def LevelBlock.reset (b : LevelBlock) : LevelBlock :=
  { b with freeIdx := 0, generation := b.generation + 1 }

/-- Allocates a new block, possibly by drawing it from the free list. -/
def LevelContext.mkBlock (ctx : LevelContext) : LevelBlockId × LevelContext :=
  match ctx.freeBlocks with
  | freeBlock :: freeBlocks =>
    (freeBlock, { ctx with freeBlocks })
  | [] =>
    let block := LevelBlock.init
    let blockId : LevelBlockId := { id := ctx.blocks.size }
    (blockId, { ctx with blocks := ctx.blocks.push block })

/--
Adds the block to the free list. Increments the generation counter to invalidate
any existing handles.
-/
def LevelContext.freeBlock (ctx : LevelContext) (bid : LevelBlockId) :
    LevelContext :=
  { ctx.modifyBlock bid LevelBlock.reset with
    freeBlocks := bid :: ctx.freeBlocks }

/-- Allocates a new block for a region. -/
def LevelContext.regionMkBlock (ctx : LevelContext) (rid : LevelRegionId) :
    LevelBlockId × LevelContext :=
  let (blockId, ctx) := ctx.mkBlock
  let ctx := ctx.modifyBlock blockId fun block => { block with region := rid }
  let ctx := ctx.modifyRegion rid fun region =>
    { region with blockIds := blockId :: region.blockIds }
  (blockId, ctx)

/--
Creates a new allocation region. By default, new allocations go into this
region.
-/
def LevelContext.pushRegion (ctx : LevelContext) :
    LevelRegionId × LevelContext :=
  let rid : LevelRegionId := { id := ctx.regions.size }
  let (bid, ctx) := ctx.mkBlock
  let ctx := ctx.modifyBlock bid fun block => { block with region := rid }
  let ctx := { ctx with regions := ctx.regions.push { blockIds := [bid] } }
  (rid, ctx)

/--
Deallocates the last region that was created with `pushRegion`.
All handles to levels contained within it become invalid.
-/
def LevelContext.popRegion (ctx : LevelContext) : LevelContext :=
  assert! ctx.regions.size > 1
  let r := ctx.regions.get! (ctx.regions.size - 1)
  let ctx := { ctx with regions := ctx.regions.pop }
  let ctx := r.blockIds.foldl (init := ctx) freeBlock
  ctx

/-- Returns true if the block has free space. -/
def LevelBlock.hasFree (block : LevelBlock) : Bool :=
  block.freeIdx.toNat < levelContextBlockSize

/--
Returns the current allocation block for the region, allocating a new
block if the current one is full.
-/
def LevelContext.regionAllocBlockId (ctx : LevelContext)
    (rid : LevelRegionId) : LevelBlockId × LevelContext :=
  let blockId := ctx.regionCurrBlockId rid
  let block := ctx.getBlock blockId
  if block.hasFree then
    (blockId, ctx)
  else
    ctx.regionMkBlock rid

/-- Allocates a level in the given region. -/
def LevelContext.regionMkLevelOffset (ctx : LevelContext) (rid : LevelRegionId)
    (u : Level LevelId) (offset : Nat) : LevelId × LevelContext :=
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
    let levelId : LevelId :=
      { idx := LevelId.mkIdx blockId index
        offset := mkOffset offset
        generation }
    (levelId, ctx)

/-- Allocates a level in the current region. -/
def LevelContext.mkLevelOffset (ctx : LevelContext)
    (u : Level LevelId) (offset : Nat) : LevelId × LevelContext :=
  let rid := ctx.currRegionId
  ctx.regionMkLevelOffset rid u offset

def LevelContext.mkMax (ctx : LevelContext) (u v : LevelId) :
    LevelId × LevelContext :=
  ctx.mkLevelOffset (Level.max u v) 0

def LevelContext.mkIPos (ctx : LevelContext) (u v : LevelId) :
    LevelId × LevelContext :=
  ctx.mkLevelOffset (Level.ipos u v) 0

def LevelContext.mkParam (ctx : LevelContext) (n : Name) :
    LevelId × LevelContext :=
  ctx.mkLevelOffset (Level.param n) 0

def LevelContext.mkMVar (ctx : LevelContext) (mvarId : LMVarId) :
    LevelId × LevelContext :=
  ctx.mkLevelOffset (Level.mvar mvarId) 0

def LevelContext.stats (ctx : LevelContext) : String :=
  let totalLevels := ctx.blocks.foldl (init := 0) fun total block =>
    total + block.freeIdx.toNat
  s!"LevelContext stats:\n\
  - {ctx.blocks.size} blocks ({ctx.freeBlocks.length} in free list)\n\
  - {ctx.regions.size} regions\n\
  - {totalLevels} level expressions"

/--
Class for monads that contain `LevelContext` state.
This provides `MonadGetLevel` and `MonadMkLevel` instances.
-/
class MonadLevelContext (m : Type → Type) where
  getLevelContext : m LevelContext
  modifyGetLevelContext {α} (f : LevelContext → α × LevelContext) : m α

@[inline]
def MonadLevelContext.modifyLevelContext {m : Type → Type} [MonadLevelContext m]
    (f : LevelContext → LevelContext) : m Unit :=
  modifyGetLevelContext fun ctx => ((), f ctx)

export MonadLevelContext (getLevelContext modifyGetLevelContext modifyLevelContext)

instance (m : Type → Type) [Monad m] [MonadLevelContext m] : MonadGetLevel m LevelId where
  getLevel u := (LevelContext.get · u) <$> getLevelContext
  getLevelOffset u := pure u.getOffset
  levelHasMVar u := (LevelContext.hasMVar · u) <$> getLevelContext
  levelHasParam u := (LevelContext.hasParam · u) <$> getLevelContext
  levelHash u := (LevelContext.getHash · u) <$> getLevelContext

instance (m : Type → Type) [Monad m] [MonadLevelContext m] : MonadMkLevel m LevelId where
  mkLevelZero := pure LevelId.zero
  mkLevelSucc u := pure u.succ
  mkLevelMax u v := modifyGetLevelContext (fun ctx => ctx.mkMax u v)
  mkLevelIPos u v := modifyGetLevelContext (fun ctx => ctx.mkIPos u v)
  mkLevelParam n := modifyGetLevelContext (fun ctx => ctx.mkParam n)
  mkLevelMVar mvarId := modifyGetLevelContext (fun ctx => ctx.mkMVar mvarId)
  mkLevelOffset u offset := pure <| u.addOffset offset

namespace LevelId
variable {m : Type → Type} [Monad m] [MonadLevelContext m]

def get (u : LevelId) : m (Level LevelId) :=
  getLevel u

def hasMVar (u : LevelId) : m Bool :=
  MonadGetLevel.levelHasMVar u

def hasParam (u : LevelId) : m Bool :=
  MonadGetLevel.levelHasParam u

def hash (u : LevelId) : m UInt64 :=
  MonadGetLevel.levelHash u

/--
Normalizes the level. Does not instantiate metavariables.
-/
def normalize (u : LevelId) : m LevelId :=
  normalizeLevel u

/--
Structural equality.
-/
def eq (u v : LevelId) : m Bool :=
  levelEq u v

/--
Level equivalence.
-/
def equiv (u v : LevelId) : m Bool :=
  levelEquiv u v

def le (u v : LevelId) : m Bool :=
  levelLE u v

end LevelId

section MonadLevelContext
variable {m : Type → Type} [Monad m] [MonadLevelContext m]

/--
Runs `f` with a new allocation region, deallocating the region at the end.
-/
def withNewLevelRegion [MonadFinally m] {α}
    (f : LevelRegionId → m α) : m α := do
  let rid ← modifyGetLevelContext (fun ctx => ctx.pushRegion)
  try
    f rid
  finally
    modifyLevelContext (fun ctx => ctx.popRegion)

end MonadLevelContext

end LilLean
