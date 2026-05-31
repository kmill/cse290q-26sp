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
is a mechanism for maintaining a stack of regions. We keep the the invariant
that older regions cannot point into newer regions. New levels can be allocated
into any region.

The handles record which block their memory is in, as well as maintaining a
generation counter to try to catch use-after-free bugs. Additionally, we
encode `Level.offset`/`Level.zero` expressions in the handle itself, for
efficiency.

The level context is designed to be somewhat performant as a persistent data
structure, since we need to be able to capture the level context for error
reporting and logging purposes. However, the level context is not intended to
be part of the backtracked state.
-/

public section

namespace LilLean

/--
Handle for a `Level` expression managed by a `LevelContext`.
-/
structure LevelId where private mk ::
  /--
  Bits 0-23: UInt24 block ID
  Bits 24-31: UInt8 index into the block
  Bits 32-47: UInt16 offset (to encode `Level.offset` in the handle)
  Bits 48-63: UInt16 generation counter (to try to detect use-after-free bugs)

  If the block ID is -1 then bits 24-63 serve as the offset of `Level.zero`.
  -/
  private idx : UInt64
  deriving BEq

instance : Hashable LevelId where
  hash := private LevelId.idx

private def levelIdBlockMask : UInt64 := ((1 <<< 24) - 1).toUInt64

def LevelId.zero : LevelId :=
  { idx := levelIdBlockMask }

instance : Inhabited LevelId := ⟨LevelId.zero⟩

/--
ID for a memory block in the `LevelContext`.
-/
private structure LevelBlockId where
  id : Nat
  deriving Inhabited

/--
ID for a region in the `LevelContext`.
-/
structure LevelRegionId where private mk ::
  /-- Unique id -/
  private uid : Nat
  /-- Index into the `LevelContext.regions` array -/
  private idx : Nat
  deriving Inhabited

instance : Ord LevelRegionId where
  compare := private fun r1 r2 => compare r1.uid r2.uid

private inductive LevelIdView where
  | zero (offset : Nat)
  | handle (blockId : LevelBlockId) (idx offset : Nat) (generation : UInt16)

@[inline]
private def LevelId.view (u : LevelId) : LevelIdView :=
  if u.idx &&& levelIdBlockMask == levelIdBlockMask then
    LevelIdView.zero (u.idx >>> 24).toNat
  else
    let blockId : LevelBlockId := { id := (u.idx &&& levelIdBlockMask).toNat }
    let idx := ((u.idx >>> 24) &&& 255).toNat
    let offset := ((u.idx >>> 32) &&& 65535).toNat
    let generation := (u.idx >>> 48).toUInt16
    LevelIdView.handle blockId idx offset generation

private instance : ToString LevelIdView where
  toString
    | .zero offset => s!"(zero {offset})"
    | .handle blockId idx offset generation =>
      s!"(handle {blockId.id}[{idx}]+{offset} @ {generation})"

instance : ToString LevelId where
  toString u := private toString u.view

@[inline]
private def LevelIdView.toLevelId : LevelIdView → LevelId
  | .zero offset =>
    assert! offset < (1 <<< 40)
    { idx := (offset.toUInt64 <<< 24) ||| levelIdBlockMask }
  | .handle blockId idx offset generation =>
    assert! blockId.id < (1 <<< 24)
    assert! offset < (1 <<< 16)
    { idx :=
      blockId.id.toUInt64
      ||| (idx.toUInt64 <<< 24)
      ||| (offset.toUInt64 <<< 32)
      ||| (generation.toUInt64 <<< 48) }

@[inline]
private def LevelIdView.addOffset (offset : Nat) : LevelIdView → LevelIdView
  | .zero offset' =>
    .zero (offset' + offset)
  | .handle blockId idx offset' generation =>
    .handle blockId idx (offset' + offset) generation

def LevelId.addOffset (u : LevelId) (offset : Nat) : LevelId :=
  if offset == 0 then u
  else (u.view.addOffset offset).toLevelId

def LevelId.succ (u : LevelId) : LevelId :=
  u.addOffset 1

private structure LevelBlock where
  /-- Region the block is associated to. -/
  regionId : LevelRegionId
  /-- Generation counter for the block. Incremented every time it is freed. -/
  generation : UInt16
  /-- Index to the first free slot in `levels`. -/
  freeIdx : Nat
  /-- Uses an `Array` for the block. Assumption: these are rarely copied. -/
  levels : Array (Level LevelId)
  /-- Cache of hashes of corresponding levels. -/
  hashes : Array UInt64

/-- Returns true if the block has free space. -/
private def LevelBlock.hasFree (block : LevelBlock) : Bool :=
  block.freeIdx < 256

private structure LevelRegion where
  regionId : LevelRegionId
  /-- Blocks owned by this region. The first block in the list is the one
  that is currently used for new allocations. -/
  blockIds : List LevelBlockId
  /-- Forwarding pointers, for promoting levels to older regions.
  See `promoteLevel`. -/
  forward : Std.HashMap LevelId LevelId := {}
  deriving Inhabited

/--
Context for allocating `Level` expressions.
-/
structure LevelContext where private mk ::
  /-- Array of all blocks, both those used by regions, and those in the
  `freeBlocks` list. -/
  private blocks : Lean.PersistentArray LevelBlock
  /-- Array of all allocation regions. -/
  private regions : Lean.PersistentArray LevelRegion
  /-- List of blocks in `blocks` that are free. -/
  private freeBlocks : List LevelBlockId
  nextRegionUId : Nat := 1
  /-- The current allocation region. Can be modified to change where levels
  are being allocated. -/
  currRegionId : LevelRegionId

def LevelRegionId.static : LevelRegionId := { uid := 0, idx := 0 }

private def LevelBlock.init : LevelBlock where
  regionId := .static
  generation := 0
  freeIdx := 0
  levels := Array.replicate 256 Level.zero
  hashes := Array.replicate 256 0

private instance : Inhabited LevelBlock := ⟨.init⟩

/--
Creates the initial level context with a single allocation region.
-/
def LevelContext.init : LevelContext where
  blocks := List.toPArray' [LevelBlock.init]
  regions := List.toPArray' [{ regionId := .static, blockIds := [{ id := 0}] }]
  freeBlocks := []
  currRegionId := .static

instance : Inhabited LevelContext := ⟨.init⟩

private def LevelContext.getBlock (ctx : LevelContext) (bid : LevelBlockId) :
    LevelBlock :=
  ctx.blocks.get! bid.id

private def LevelContext.modifyBlock (ctx : LevelContext) (bid : LevelBlockId)
    (f : LevelBlock → LevelBlock) : LevelContext :=
  { ctx with blocks := ctx.blocks.modify bid.id f }

private def LevelContext.getRegion (ctx : LevelContext) (rid : LevelRegionId) :
    LevelRegion :=
  let region := ctx.regions.get! rid.idx
  assert! region.regionId.uid == rid.uid
  region

private def LevelContext.modifyRegion (ctx : LevelContext) (rid : LevelRegionId)
    (f : LevelRegion → LevelRegion) : LevelContext :=
  { ctx with regions := ctx.regions.modify rid.idx f }

def LevelContext.getRegionId (ctx : LevelContext) (u : LevelId) :
    LevelRegionId :=
  match u.view with
  | .zero .. => .static
  | .handle blockId .. => (ctx.getBlock blockId).regionId

def LevelContext.get (ctx : LevelContext) (u : LevelId) : Level LevelId :=
  match u.view with
  | .zero offset =>
    if offset == 0 then Level.zero else Level.offset LevelId.zero offset
  | .handle blockId idx offset generation =>
    if offset == 0 then
      let block := ctx.getBlock blockId
      assert! block.generation == generation
      block.levels[idx]!
    else
      Level.offset (LevelIdView.handle blockId idx 0 generation).toLevelId offset

def LevelContext.getHash (ctx : LevelContext) (u : LevelId) : UInt64 :=
  match u.view with
  | .zero offset => Level.hashConst offset
  | .handle blockId idx offset generation =>
    let block := ctx.getBlock blockId
    assert! block.generation == generation
    let h := block.hashes[idx]!
    if offset == 0 then
      h
    else
      Level.hashOffset h offset

/-- Gets the block that the region is allocating into. -/
private def LevelContext.regionCurrBlockId (ctx : LevelContext)
    (rid : LevelRegionId) : LevelBlockId :=
  (ctx.getRegion rid).blockIds.head!

/-- Resets the free index and increments the generation counter. -/
private def LevelBlock.reset (b : LevelBlock) : LevelBlock :=
  { b with freeIdx := 0, generation := b.generation + 1 }

/-- Allocates a new block, possibly by drawing it from the free list. -/
private def LevelContext.newBlock (ctx : LevelContext) :
    LevelBlockId × LevelContext :=
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
private def LevelContext.freeBlock (ctx : LevelContext) (bid : LevelBlockId) :
    LevelContext :=
  { ctx.modifyBlock bid LevelBlock.reset with
    freeBlocks := bid :: ctx.freeBlocks }

/-- Allocates a new block for a region. -/
private def LevelContext.regionNewBlock (ctx : LevelContext)
    (rid : LevelRegionId) : LevelBlockId × LevelContext :=
  let (blockId, ctx) := ctx.newBlock
  let ctx := ctx.modifyBlock blockId fun block => { block with regionId := rid }
  let ctx := ctx.modifyRegion rid fun region =>
    { region with blockIds := blockId :: region.blockIds }
  (blockId, ctx)

private def LevelContext.newRegionId (ctx : LevelContext) :
    LevelRegionId × LevelContext :=
  let uid := ctx.nextRegionUId
  ({ uid, idx := ctx.regions.size }, { ctx with nextRegionUId := uid + 1 })

/--
Creates a new allocation region. By default, new allocations go into this
region.
-/
def LevelContext.pushRegion (ctx : LevelContext) :
    LevelRegionId × LevelContext :=
  let (regionId, ctx) := ctx.newRegionId
  let (bid, ctx) := ctx.newBlock
  let ctx := ctx.modifyBlock bid fun block => { block with regionId }
  let ctx := { ctx with
    regions := ctx.regions.push { regionId, blockIds := [bid] } }
  (regionId, ctx)

/--
Deallocates the last region that was created with `pushRegion`.
All handles to levels contained within it become invalid.
The region id must be the region being deallocated.
-/
def LevelContext.popRegion (ctx : LevelContext)
    (rid : LevelRegionId) :
    LevelContext :=
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
private def LevelContext.regionAllocBlockId (ctx : LevelContext)
    (rid : LevelRegionId) : LevelBlockId × LevelContext :=
  let blockId := ctx.regionCurrBlockId rid
  if (ctx.getBlock blockId).hasFree then
    (blockId, ctx)
  else
    ctx.regionNewBlock rid

/-- Allocates a level in the given region. -/
def LevelContext.regionMkLevel (ctx : LevelContext) (rid : LevelRegionId)
    (u : Level LevelId) : LevelId × LevelContext :=
  match u with
  | .zero => (LevelId.zero, ctx)
  | .offset u' c => (u'.addOffset c, ctx)
  | _ =>
    let hash := u.hashCore ctx.getHash
    let (blockId, ctx) := ctx.regionAllocBlockId rid
    let block := ctx.getBlock blockId
    assert! block.hasFree
    let { freeIdx := idx, generation, .. } := block
    let ctx := ctx.modifyBlock blockId fun block =>
      { block with
        freeIdx := block.freeIdx + 1
        levels := block.levels.set! idx u
        hashes := block.hashes.set! idx hash }
    let levelId : LevelId := LevelIdView.toLevelId <|
      .handle blockId idx 0 generation
    (levelId, ctx)

/-- Allocates a level in the current region. -/
def LevelContext.mkLevel (ctx : LevelContext)
    (u : Level LevelId) : LevelId × LevelContext :=
  ctx.regionMkLevel ctx.currRegionId u

def LevelContext.stats (ctx : LevelContext) : String :=
  let totalLevels := ctx.blocks.foldl (init := 0) fun total block =>
    total + block.freeIdx
  s!"LevelContext stats:\n\
  - {ctx.blocks.size} blocks ({ctx.freeBlocks.length} in free list)\n\
  - {ctx.regions.size} regions\n\
  - {totalLevels} total level expressions"

@[inline] def LevelContext.levelGetter (ctx : LevelContext) :
    LevelGetter LevelId where
  get := ctx.get
  hash := ctx.getHash

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

export MonadLevelContext
  (getLevelContext modifyGetLevelContext modifyLevelContext)

instance (m : Type → Type) [Monad m] [MonadLevelContext m] :
    MonadGetLevel m LevelId where
  getLevelGetter := LevelContext.levelGetter <$> getLevelContext

instance (m : Type → Type) [Monad m] [MonadLevelContext m] :
    MonadMkLevel m LevelId where
  mkLevel u := modifyGetLevelContext (fun ctx => ctx.mkLevel u)

namespace LevelId
variable {m : Type → Type} [Monad m] [MonadLevelContext m]

def get (u : LevelId) : m (Level LevelId) :=
  getLevel u

def hasMVar (u : LevelId) : m Bool :=
  levelHasMVar u

def hasParam (u : LevelId) : m Bool :=
  levelHasParam u

def hash (u : LevelId) : m UInt64 :=
  levelHash u

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

/-- Monad for doing `LevelContext` manipulations. -/
abbrev LevelContext.M := StateM LevelContext

instance : MonadLevelContext LevelContext.M where
  getLevelContext := get
  modifyGetLevelContext := modifyGet

section Promote

partial def promoteLevelCore (u : LevelId) : LevelContext.M LevelId := do
  match u.view with
  | .zero .. => return u
  | .handle blockId idx offset generation =>
    let ctx ← getLevelContext
    let block := ctx.getBlock blockId
    assert! block.generation == generation
    let rid := block.regionId
    if (compare rid ctx.currRegionId).isLE then
      return u
    else
      let u' := (LevelIdView.handle blockId idx 0 generation).toLevelId
      if let some u'' := (ctx.getRegion rid).forward[u']? then
        (LevelId.addOffset · offset) <$> promoteLevelCore u''
      else
        let u'' ← mkLevel =<< (← u'.get).mapM promoteLevelCore
        modifyLevelContext fun ctx => ctx.modifyRegion rid fun region =>
          { region with forward := region.forward.insert u' u'' }
        return LevelId.addOffset u'' offset

/--
If `u` is in a newer region than the current region, copies it into the current
region, returning the copied level.

This is intended to be used with `withSetCurrLevelRegion`, and it is like a
tracing garbage collection step before returning from `withNewLevelRegion`.
-/
partial def promoteLevel {m : Type → Type} [MonadLevelContext m]
    (u : LevelId) : m LevelId :=
  modifyGetLevelContext <| (promoteLevelCore u).run

end Promote

section MonadLevelContext
variable {m : Type → Type} [Monad m] [MonadLevelContext m]

/--
Temporarily sets the current level allocation region while executing `x`.
-/
def withSetCurrLevelRegion [MonadFinally m] {α}
    (regionId : LevelRegionId) (x : m α) : m α := do
  let oldRegionId ← modifyGetLevelContext (fun ctx =>
    (ctx.currRegionId, { ctx with currRegionId := regionId }))
  try
    x
  finally
    modifyLevelContext (fun ctx => { ctx with currRegionId := oldRegionId })

/--
Runs `f` with a new allocation region, deallocating the region at the end.
-/
def withNewLevelRegion [MonadFinally m] {α}
    (f : LevelRegionId → m α) : m α := do
  let rid ← modifyGetLevelContext (fun ctx => ctx.pushRegion)
  try
    withSetCurrLevelRegion rid do f rid
  finally
    modifyLevelContext (fun ctx => ctx.popRegion rid)

end MonadLevelContext

end LilLean
