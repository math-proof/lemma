/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives
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

end TempRangeInBounds
end CPythonListsort
