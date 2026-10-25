/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean -/

import Def.CPythonListsort.Code.Transcription.Gallop.Part2
import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Theorem.CPythonListsort.Code.Transcription.MergeHi
/-!
# Right-to-left stable merge transcription

This module transcribes CPython's `merge_hi` from the pinned
`Objects/listobject.c`.  The active list remains in `MergeState.data`; the
shorter right run is copied into `MergeState.a`, whose optional cells retain
the distinction between allocated and initialized temporary storage.

The ordinary and galloping loops are represented by a fuel-bounded phase
machine.  Modeled assertion or bounds failures return `none`.  Exhaustion of
the explicit loop or of a nested gallop is instead observable through
`fuelExhausted`, while rejection by `merge_getmem` retains C's `-1` result.

Equality selects B while filling backward, leaving the equal A entry before it
in final forward order.  Galloping retains C's `na == 0` and `nb == 0` branches
for inconsistent but total comparators, including the `na - k` and `nb - k`
conversions from insertion indices to backward block lengths.

Version one has no comparator-error result.  CPython's comparator-error jumps
to `Fail` are deliberately absent, while the temp-to-data copyback shared by
C's `Succeed` and `Fail` labels remains on successful exits.  Distinct
temp/data block copies model `sortslice_memcpy`; blocks moved within `data` use
overlap-safe `SortSlice.memmove?`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Read one initialized logical entry from temporary merge storage. -/
def mergeHiTempRead? (storage : TempStorage κ ν) (index : Int) :
    Option (SortSliceEntry κ ν) :=
  if 0 ≤ index then
    match storage.cells[index.toNat]? with
    | some (some entry) => some entry
    | _ => none
  else
    none

/-- Initialize or replace one in-bounds logical temporary entry. -/
def mergeHiTempWrite? (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) : Option (TempStorage κ ν) :=
  if hnonnegative : 0 ≤ index then
    let i := index.toNat
    if hinBounds : i < storage.cells.size then
      some { storage with cells := storage.cells.set i (some entry) }
    else
      none
  else
    none

/-- Copy one main-list entry into temporary storage without advancing cursors. -/
def mergeHiCopyDataToTemp? (state : MergeState κ ν) (dst src : Int) :
    Option (MergeState κ ν) := do
  let entry ← state.data.read? src
  let storage ← mergeHiTempWrite? state.a dst entry
  pure { state with a := storage }

/-- Copy one initialized temporary entry into the main list without advancing
cursors. -/
def mergeHiCopyTempToData? (state : MergeState κ ν) (dst src : Int) :
    Option (MergeState κ ν) := do
  let entry ← mergeHiTempRead? state.a src
  let data ← state.data.write? dst entry
  pure { state with data := data }

/-- Forward bulk copy from main data to distinct temporary storage.  The
recursive memcpy implementation itself requires a pinned call-site tag and a
proof of its physical direction.  Its one-cell primitive is hardwired
data-to-temporary and is used only by this tagged bulk executor. -/
def mergeHiMemcpyDataToTemp?
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main }) :
    Nat → MergeState κ ν → Int → Int → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, dst, src => do
      let state ← mergeHiCopyDataToTemp? state dst src
      mergeHiMemcpyDataToTemp? site hDirection count state (dst + 1) (src + 1)

/-- Forward bulk copy from temporary storage to distinct main data.  No raw
recursive temp-to-data memcpy helper exists below this tagged interface.  The
one-cell primitive is hardwired temporary-to-data and also models ordinary
`sortslice_copy`. -/
def mergeHiMemcpyTempToData?
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary }) :
    Nat → MergeState κ ν → Int → Int → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, dst, src => do
      let state ← mergeHiCopyTempToData? state dst src
      mergeHiMemcpyTempToData? site hDirection count state (dst + 1) (src + 1)

/-- Every cell in a signed temporary range is initialized and readable. -/
def MergeHiTempRangeInitialized (storage : TempStorage κ ν)
    (source : Int) (count : Nat) : Prop :=
  ∀ i, i < count →
    ∃ entry,
      mergeHiTempRead? storage (source + Int.ofNat i) = some entry

def mergeHiInitializedTempPrefixLoop? :
    Nat → TempStorage κ ν → Nat → Array (SortSliceEntry κ ν) →
      Option (Array (SortSliceEntry κ ν))
  | 0, _, _, entries => some entries
  | count + 1, storage, index, entries => do
      let entry ← mergeHiTempRead? storage (Int.ofNat index)
      mergeHiInitializedTempPrefixLoop? count storage (index + 1)
        (entries.push entry)

/-- Expose the initialized prefix of `ms->a` to the existing gallop
transcription.  Uninitialized capacity beyond `count` is deliberately not
read. -/
def initializedTempPrefix? (storage : TempStorage κ ν) (count : Nat) :
    Option (SortSlice κ ν) := do
  let entries ← mergeHiInitializedTempPrefixLoop? count storage 0 #[]
  pure { entries := entries }

/-- Every logical cell in the prefix is initialized and therefore readable.
This is the exact domain condition for `initializedTempPrefix?`; capacity alone
is deliberately insufficient because freshly grown storage contains `none`. -/
def MergeHiTempPrefixInitialized (storage : TempStorage κ ν)
    (count : Nat) : Prop :=
  MergeHiTempRangeInitialized storage 0 count

end CPythonListsort
