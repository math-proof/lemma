/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.MergeMemcpyProvenance

/-!
# Typed trace support for merge movement

The merge transcriptions keep the main list in `MergeState.data` and the
shorter run in `MergeState.a`.  `SortSlice`'s two-store movement API cannot be
used directly for that pair because temporary storage has a distinct carrier,
an explicit live/released backing state, and possibly-uninitialized cells.

This module supplies the common traced movement layer used by both merge
directions.  Every access goes through a state-derived wrapper from
`AccessTrace`; in particular, callers cannot manufacture the temporary backing
or either extent.  Bulk `memcpy` executors retain a classified call-site tag,
its exact direction, and its distinct-backing certificate at every recursive
call.  Key accesses for the complete range precede the optional synchronized-
values phase, which is selected solely by `state.a.hasValues`.
-/

namespace CPythonListsort

universe u v

open SortSlice

/-! ## Call-site provenance -/

/-- The closed union of the six classified merge `memcpy` sites. -/
inductive MergeMemcpySite where
  | lo (site : MergeLoMemcpyCallsite)
  | hi (site : MergeHiMemcpyCallsite)
  deriving DecidableEq, Repr

namespace MergeMemcpySite

/-- Physical source and destination regions of a classified site. -/
def backings : MergeMemcpySite → MergeMemcpyBackings
  | .lo site => site.backings
  | .hi site => site.backings

/-- The exported provenance theorem covers every site in the closed union. -/
theorem distinct (site : MergeMemcpySite) : site.backings.Distinct := by
  cases site with
  | lo site =>
      exact
        (mergeMemcpyCallsiteProvenance (κ := Unit) (ν := Unit))
          |>.mergeLoCallsitesDistinct site
  | hi site =>
      exact
        (mergeMemcpyCallsiteProvenance (κ := Unit) (ν := Unit))
          |>.mergeHiCallsitesDistinct site

/-- A classified main-to-temporary site, with provenance kept explicit. -/
structure MainToTempPermit (site : MergeMemcpySite) : Prop where
  direction : site.backings =
    { destination := .temporary, source := .main }
  distinctBacking : site.backings.Distinct

/-- A classified temporary-to-main site, with provenance kept explicit. -/
structure TempToMainPermit (site : MergeMemcpySite) : Prop where
  direction : site.backings =
    { destination := .main, source := .temporary }
  distinctBacking : site.backings.Distinct

end MergeMemcpySite

/-! ## Signed temporary ranges and backward cursors -/

/-- A signed index denotes an allocated logical temporary cell. -/
def TempIndexInBounds (storage : TempStorage κ ν) (index : Int) : Prop :=
  0 ≤ index ∧ index < Int.ofNat storage.cells.size

/-- The half-open signed range `[start, start + count)` lies in temporary
storage.  The empty range admits the one-past endpoint. -/
def TempRangeInBounds (storage : TempStorage κ ν) (start : Int)
    (count : Nat) : Prop :=
  0 ≤ start ∧ start + Int.ofNat count ≤ Int.ofNat storage.cells.size

/-- Backward merge cursors may be at a live cell or at the one-before-beginning
sentinel produced after copying cell zero.  A dereference still requires the
stronger `0 ≤ cursor` fact. -/
def BackwardCursorInRange (extent : Nat) (cursor : Int) : Prop :=
  -1 ≤ cursor ∧ cursor < Int.ofNat extent

namespace TempRangeInBounds

/-- Every cell in a temporary range is initialized. -/
def TempRangeInitialized (storage : TempStorage κ ν) (start : Int)
    (count : Nat) : Prop :=
  ∀ offset : Nat, offset < count →
    ∃ entry, (TraceResult.tempPayloadRead? storage
      (start + Int.ofNat offset)).erase = some entry

/-- Every initialized entry in a temporary range agrees with the explicit
values-pointer mode. -/
def TempRangeValuesMode (storage : TempStorage κ ν) (start : Int)
    (count : Nat) : Prop :=
  ∀ offset : Nat, offset < count →
    ∃ entry,
      (TraceResult.tempPayloadRead? storage
        (start + Int.ofNat offset)).erase = some entry ∧
      SortSlice.EntryMatchesValuesMode storage.hasValues entry

/-! ## Explicit untraced cores -/

/-- Untraced temporary read corresponding exactly to the typed wrapper. -/
def mergeTempRead? (storage : TempStorage κ ν) (index : Int) :
    Option (SortSliceEntry κ ν) :=
  if 0 ≤ index then storage.cells[index.toNat]?.bind id else none

/-- Untraced temporary write corresponding exactly to the typed wrapper. -/
def mergeTempWrite? (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) : Option (TempStorage κ ν) :=
  if 0 ≤ index ∧ index.toNat < storage.cells.size then
    some { storage with
      cells := storage.cells.setIfInBounds index.toNat (some entry) }
  else
    none

/-- One atomic main-to-temporary logical-cell copy. -/
def mainToTempCell? (state : MergeState κ ν) (tempDst mainSrc : Int) :
    Option (MergeState κ ν) := do
  let entry ← state.data.read? mainSrc
  let storage ← mergeTempWrite? state.a tempDst entry
  pure { state with a := storage }

/-- One atomic temporary-to-main logical-cell copy. -/
def tempToMainCell? (state : MergeState κ ν) (mainDst tempSrc : Int) :
    Option (MergeState κ ν) := do
  let entry ← mergeTempRead? state.a tempSrc
  let data ← state.data.write? mainDst entry
  pure { state with data := data }

/-- Forward distinct-backing main-to-temporary copy. -/
def mainToTempMemcpy? :
    Nat → MergeState κ ν → Int → Int → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, tempDst, mainSrc => do
      let state ← mainToTempCell? state tempDst mainSrc
      mainToTempMemcpy? count state (tempDst + 1) (mainSrc + 1)

/-- Forward distinct-backing temporary-to-main copy. -/
def tempToMainMemcpy? :
    Nat → MergeState κ ν → Int → Int → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, mainDst, tempSrc => do
      let state ← tempToMainCell? state mainDst tempSrc
      tempToMainMemcpy? count state (mainDst + 1) (tempSrc + 1)

/-- Main-data overlap-safe movement lifted back into `MergeState`. -/
def mainDataMemmove? (state : MergeState κ ν) (dst src : Int) (count : Nat) :
    Option (MergeState κ ν) := do
  let data ← state.data.memmove? dst src count
  pure { state with data := data }

/-! ## Typed one-cell phases -/

/-- Key phase of one main-to-temporary copy. -/
def mainToTempKeyTraced? (state : MergeState κ ν) (tempDst mainSrc : Int) :
    TraceResult (MergeState κ ν) :=
  (TraceResult.sortSliceKeysRead? state.data mainSrc).bind fun entry =>
    (TraceResult.tempPayloadWrite? state.a tempDst entry).map fun storage =>
      { state with a := storage }

/-- Optional synchronized-values phase of one main-to-temporary copy. -/
def mainToTempValuesTraced? (state : MergeState κ ν)
    (tempDst mainSrc : Int) : TraceResult (MergeState κ ν) :=
  (TraceResult.sortSliceValuesRead? state.data mainSrc).bind fun entry =>
    (TraceResult.tempPayloadWrite? state.a tempDst entry).map fun storage =>
      { state with a := storage }

/-- One source-language main-to-temporary copy.  The values phase starts from
the original paired state, as in `SortSlice.copyFromTraced?`, because either
physical phase represents the same atomic paired-entry update. -/
def mainToTempCellTraced? (state : MergeState κ ν) (tempDst mainSrc : Int) :
    TraceResult (MergeState κ ν) :=
  (mainToTempKeyTraced? state tempDst mainSrc).bind fun keyResult =>
    if state.a.hasValues then
      mainToTempValuesTraced? state tempDst mainSrc
    else
      TraceResult.pure keyResult

/-- Key phase of one temporary-to-main copy. -/
def tempToMainKeyTraced? (state : MergeState κ ν) (mainDst tempSrc : Int) :
    TraceResult (MergeState κ ν) :=
  (TraceResult.tempPayloadRead? state.a tempSrc).bind fun entry =>
    (TraceResult.sortSliceKeysWrite? state.data mainDst entry).map fun data =>
      { state with data := data }

/-- Optional synchronized-values phase of one temporary-to-main copy. -/
def tempToMainValuesTraced? (state : MergeState κ ν)
    (mainDst tempSrc : Int) : TraceResult (MergeState κ ν) :=
  (TraceResult.tempPayloadRead? state.a tempSrc).bind fun entry =>
    (TraceResult.sortSliceValuesWrite? state.data mainDst entry).map fun data =>
      { state with data := data }

/-- One source-language temporary-to-main copy. -/
def tempToMainCellTraced? (state : MergeState κ ν) (mainDst tempSrc : Int) :
    TraceResult (MergeState κ ν) :=
  (tempToMainKeyTraced? state mainDst tempSrc).bind fun keyResult =>
    if state.a.hasValues then
      tempToMainValuesTraced? state mainDst tempSrc
    else
      TraceResult.pure keyResult

/-! ## Recursively tagged bulk phases -/

/-- Complete key phase of main-to-temporary `memcpy`.  The site and both
proofs remain arguments of the recursive call. -/
def mainToTempKeysTraced? (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) :
    Nat → MergeState κ ν → Int → Int → TraceResult (MergeState κ ν)
  | 0, state, _, _ => TraceResult.pure state
  | count + 1, state, tempDst, mainSrc =>
      (mainToTempKeyTraced? state tempDst mainSrc).bind fun state =>
        mainToTempKeysTraced? site permit count state
          (tempDst + 1) (mainSrc + 1)

/-- Complete optional-values phase of main-to-temporary `memcpy`. -/
def mainToTempValuesPhaseTraced? (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) :
    Nat → MergeState κ ν → Int → Int → TraceResult (MergeState κ ν)
  | 0, state, _, _ => TraceResult.pure state
  | count + 1, state, tempDst, mainSrc =>
      (mainToTempValuesTraced? state tempDst mainSrc).bind fun state =>
        mainToTempValuesPhaseTraced? site permit count state
          (tempDst + 1) (mainSrc + 1)

/-- Tagged main-to-temporary `memcpy`, with all key events before all optional
values events. -/
def mainToTempMemcpyTraced? (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    TraceResult (MergeState κ ν) :=
  (mainToTempKeysTraced? site permit count state tempDst mainSrc).bind
    fun keyResult =>
      if state.a.hasValues then
        mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc
      else
        TraceResult.pure keyResult

/-- Complete key phase of temporary-to-main `memcpy`. -/
def tempToMainKeysTraced? (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) :
    Nat → MergeState κ ν → Int → Int → TraceResult (MergeState κ ν)
  | 0, state, _, _ => TraceResult.pure state
  | count + 1, state, mainDst, tempSrc =>
      (tempToMainKeyTraced? state mainDst tempSrc).bind fun state =>
        tempToMainKeysTraced? site permit count state
          (mainDst + 1) (tempSrc + 1)

/-- Complete optional-values phase of temporary-to-main `memcpy`. -/
def tempToMainValuesPhaseTraced? (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) :
    Nat → MergeState κ ν → Int → Int → TraceResult (MergeState κ ν)
  | 0, state, _, _ => TraceResult.pure state
  | count + 1, state, mainDst, tempSrc =>
      (tempToMainValuesTraced? state mainDst tempSrc).bind fun state =>
        tempToMainValuesPhaseTraced? site permit count state
          (mainDst + 1) (tempSrc + 1)

/-- Tagged temporary-to-main `memcpy`, with all key events before all optional
values events. -/
def tempToMainMemcpyTraced? (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    TraceResult (MergeState κ ν) :=
  (tempToMainKeysTraced? site permit count state mainDst tempSrc).bind
    fun keyResult =>
      if state.a.hasValues then
        tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc
      else
        TraceResult.pure keyResult

/-- Existing overlap-safe main-data movement, lifted through the state-derived
values mode. -/
def mainDataMemmoveTraced? (state : MergeState κ ν)
    (dst src : Int) (count : Nat) : TraceResult (MergeState κ ν) :=
  (SortSlice.memmoveTraced? state.a.hasValues state.data dst src count).map
    fun data => { state with data := data }

/-! ## Structural frame -/

/-- Fields and extents unchanged by every movement primitive in this module.
The main contents and temporary contents are intentionally absent. -/
structure MergeMovementFrame (before after : MergeState κ ν) : Prop where
  minGallop : after.min_gallop = before.min_gallop
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempSize : after.a.cells.size = before.a.cells.size
  tempBacking : after.a.backing = before.a.backing
  tempValuesMode : after.a.hasValues = before.a.hasValues
  alloced : after.alloced = before.alloced
  pending : after.pending = before.pending
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeMovementFrame

/-! ## Absence of control-flow events -/

/-- A local movement trace contains neither a fuel marker nor pending pushes. -/
def MovementAccessOnly (execution : TraceResult α) : Prop :=
  execution.trace.fuelExhausted = false ∧ execution.trace.pushDepths = []

namespace MovementAccessOnly

theorem initialized {storage : TempStorage κ ν} {start : Int} {count : Nat}
    (h : TempRangeValuesMode storage start count) :
    TempRangeInitialized storage start count := by
  intro offset hoffset
  rcases h offset hoffset with ⟨entry, hread, _⟩
  exact ⟨entry, hread⟩

/-! ## Common trace safety -/

/-- A trace contains an access of the requested kind to the requested region. -/
def AccessTrace.HasAccess (trace : AccessTrace) (kind : AccessKind)
    (region : AccessRegion) : Prop :=
  ∃ event ∈ trace.accesses, event.kind = kind ∧ event.region = region

/-- A trace contains a temporary-payload access of the requested kind.  The
backing observed by the event remains existentially visible. -/
def AccessTrace.HasTempAccess (trace : AccessTrace) (kind : AccessKind) : Prop :=
  ∃ backing, trace.HasAccess kind (.tempPayload backing)

namespace AccessTrace.HasAccess

/-- Complete local trace obligations shared by all merge movements. -/
structure MovementTraceSafe (execution : TraceResult α) : Prop where
  fuel : execution.trace.fuelExhausted = false
  noPushes : execution.trace.pushDepths = []
  bounds : execution.trace.allAccessesInBounds
  tempLive : execution.trace.tempPayloadAccessesLive

namespace MovementTraceSafe

theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (value : α) (hresult : current.result = some value)
    (hcurrent : MovementTraceSafe current)
    (hnext : MovementTraceSafe (next value)) :
    MovementTraceSafe (current.bind next) := by
  rcases hcurrent with ⟨hcurrentFuel, hcurrentPush, hcurrentBounds, hcurrentLive⟩
  rcases hnext with ⟨hnextFuel, hnextPush, hnextBounds, hnextLive⟩
  constructor
  · simp [TraceResult.trace_bind, hresult, hcurrentFuel, hnextFuel]
  · simp [TraceResult.trace_bind, hresult, AccessTrace.compose,
      hcurrentPush, hnextPush]
  · rw [TraceResult.trace_bind, hresult,
      AccessTrace.allAccessesInBounds_compose]
    exact ⟨hcurrentBounds, hnextBounds⟩
  · rw [TraceResult.trace_bind, hresult,
      AccessTrace.tempPayloadAccessesLive_compose]
    exact ⟨hcurrentLive, hnextLive⟩

end MovementTraceSafe

/-! ## Public aggregate bulk contracts -/

structure MainToTempMemcpyPost
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state result : MergeState κ ν) (tempDst mainSrc : Int) : Prop where
  success :
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).result =
      some result
  traceSafe :
    MovementTraceSafe
      (mainToTempMemcpyTraced? site permit count state tempDst mainSrc)
  exactErasure :
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).erase =
      mainToTempMemcpy? count state tempDst mainSrc
  frame : MergeMovementFrame state result
  tempInvariant : TempStorageInv result.a result.alloced
  tempLive : result.a.Live
  valuesMode : SortSlice.ValuesModeInvariant result.a.hasValues result.data
  initialized : TempRangeInitialized result.a tempDst count
  tempValuesMode : TempRangeValuesMode result.a tempDst count
  provenance : site.backings.Distinct
  /-- The complete generic `sortslice_memcpy` safety boundary used by this
  classified call site: distinct backing is admissible, while an overlapping
  same-backing request is rejected with an empty trace. -/
  provenanceContract : MergeMemcpyCallsiteProvenanceContract κ ν
  phaseOrder :
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).trace.accesses =
      (mainToTempKeysTraced? site permit count state tempDst mainSrc).trace.accesses ++
        (if state.a.hasValues then
          (mainToTempValuesPhaseTraced? site permit count state tempDst
            mainSrc).trace.accesses
        else [])
  inputKeyEvent : 0 < count →
    (mainToTempMemcpyTraced? site permit count state tempDst
      mainSrc).trace.HasAccess .read .inputKeys
  tempWriteEvent : 0 < count →
    (mainToTempMemcpyTraced? site permit count state tempDst
      mainSrc).trace.HasTempAccess .write
  synchronizedValuesEvent : 0 < count → state.a.hasValues = true →
    (mainToTempMemcpyTraced? site permit count state tempDst
      mainSrc).trace.HasAccess .read .synchronizedValues
  nonempty : 0 < count →
    (mainToTempMemcpyTraced? site permit count state tempDst
      mainSrc).trace.accesses ≠ []

structure TempToMainMemcpyPost
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state result : MergeState κ ν) (mainDst tempSrc : Int) : Prop where
  success :
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).result =
      some result
  traceSafe :
    MovementTraceSafe
      (tempToMainMemcpyTraced? site permit count state mainDst tempSrc)
  exactErasure :
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).erase =
      tempToMainMemcpy? count state mainDst tempSrc
  frame : MergeMovementFrame state result
  tempInvariant : TempStorageInv result.a result.alloced
  tempLive : result.a.Live
  valuesMode : SortSlice.ValuesModeInvariant result.a.hasValues result.data
  initialized : TempRangeInitialized result.a tempSrc count
  tempValuesMode : TempRangeValuesMode result.a tempSrc count
  provenance : site.backings.Distinct
  /-- The complete generic `sortslice_memcpy` safety boundary used by this
  classified call site: distinct backing is admissible, while an overlapping
  same-backing request is rejected with an empty trace. -/
  provenanceContract : MergeMemcpyCallsiteProvenanceContract κ ν
  phaseOrder :
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).trace.accesses =
      (tempToMainKeysTraced? site permit count state mainDst tempSrc).trace.accesses ++
        (if state.a.hasValues then
          (tempToMainValuesPhaseTraced? site permit count state mainDst
            tempSrc).trace.accesses
        else [])
  tempReadEvent : 0 < count →
    (tempToMainMemcpyTraced? site permit count state mainDst
      tempSrc).trace.HasTempAccess .read
  inputKeyEvent : 0 < count →
    (tempToMainMemcpyTraced? site permit count state mainDst
      tempSrc).trace.HasAccess .write .inputKeys
  synchronizedValuesEvent : 0 < count → state.a.hasValues = true →
    (tempToMainMemcpyTraced? site permit count state mainDst
      tempSrc).trace.HasAccess .write .synchronizedValues
  nonempty : 0 < count →
    (tempToMainMemcpyTraced? site permit count state mainDst
      tempSrc).trace.accesses ≠ []

/-! ## Main-data memmove aggregate contract -/

private def MovementTempLive (execution : TraceResult α) : Prop :=
  execution.trace.tempPayloadAccessesLive

namespace MovementTempLive

theorem pure (value : α) : MovementTempLive (TraceResult.pure value) :=
  AccessTrace.tempPayloadAccessesLive_empty

theorem map (current : TraceResult α) (transform : α → β)
    (h : MovementTempLive current) : MovementTempLive (current.map transform) := by
  exact h

theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (hcurrent : MovementTempLive current)
    (hnext : ∀ value, MovementTempLive (next value)) :
    MovementTempLive (current.bind next) := by
  cases hresult : current.result with
  | none => simpa [MovementTempLive, TraceResult.trace_bind, hresult] using hcurrent
  | some value =>
      rw [MovementTempLive, TraceResult.trace_bind, hresult,
        AccessTrace.tempPayloadAccessesLive_compose]
      exact ⟨hcurrent, hnext value⟩

end MovementTempLive

/-! ## Main-data one-cell decrement copy -/

/-- State-level wrapper around the shared-store decrementing copy.  Cursor
arithmetic is signed, so copying cell zero legitimately returns `-1`. -/
def mainDataCopyDecrTraced? (state : MergeState κ ν) (dst src : Int) :
    TraceResult (MergeHiDataCursorResult κ ν) :=
  (SortSlice.copyDecrTraced? state.a.hasValues state.data dst src).map
    fun copied =>
      { state := { state with data := copied.slice }
        dst := copied.dst
        src := copied.src }

structure MainDataCopyDecrPost (state : MergeState κ ν) (dst src : Int)
    (result : MergeHiDataCursorResult κ ν) : Prop where
  success : (mainDataCopyDecrTraced? state dst src).result = some result
  traceSafe : MovementTraceSafe (mainDataCopyDecrTraced? state dst src)
  exactErasure : (mainDataCopyDecrTraced? state dst src).erase =
    mergeHiCopyDataDecr? state dst src
  frame : MergeMovementFrame state result.state
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  dstDecrement : result.dst = dst - 1
  srcDecrement : result.src = src - 1

structure MainDataMemmovePost (state result : MergeState κ ν)
    (dst src : Int) (count : Nat) : Prop where
  success : (mainDataMemmoveTraced? state dst src count).result = some result
  traceSafe : MovementTraceSafe (mainDataMemmoveTraced? state dst src count)
  exactErasure : (mainDataMemmoveTraced? state dst src count).erase =
    mainDataMemmove? state dst src count
  frame : MergeMovementFrame state result
  tempInvariant : TempStorageInv result.a result.alloced
  tempLive : result.a.Live
  valuesMode : SortSlice.ValuesModeInvariant result.a.hasValues result.data
  phaseOrder :
    (mainDataMemmoveTraced? state dst src count).trace.accesses =
      match SortSlice.memmoveDirection dst src with
      | .forward =>
          (SortSlice.memmoveForwardKeysTraced? count state.data dst
            src).trace.accesses ++
            if state.a.hasValues then
              (SortSlice.memmoveForwardValuesTraced? count state.data dst
                src).trace.accesses
            else []
      | .backward =>
          (SortSlice.memmoveBackwardKeysTraced? count state.data dst
            src).trace.accesses ++
            if state.a.hasValues then
              (SortSlice.memmoveBackwardValuesTraced? count state.data dst
                src).trace.accesses
            else []
