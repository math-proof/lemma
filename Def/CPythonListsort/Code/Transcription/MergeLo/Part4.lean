/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean -/

import Def.CPythonListsort.Code.Transcription.Gallop.Part2
import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Theorem.CPythonListsort.Code.Transcription.MergeLo
/-!
# Left-to-right merge transcription

This module transcribes CPython's `merge_lo`.  The main list remains in
`MergeState.data`; the shorter left run is copied into `MergeState.a` before
the merge starts.  Invalid assertion inputs, failed modeled accesses, and
invalid nested gallop calls return `none`.  The allocation guard and bounded
loop exhaustion remain observable and distinct in `MergeLoResult`.

The ordinary and galloping loops are represented by an explicit phase
machine.  Every recursive step consumes at least one live run entry, so the
input-size fuel is exposed only through the result flag and not as a caller
parameter.  Equality selects A while merging forward.  Galloping preserves
the C branch where an inconsistent but total comparator can consume all of A.

Version one has a pure Boolean comparator, so CPython's comparator-error jumps
to `Fail` and their negative result are deliberately absent.  The physical
temp-to-data copyback shared by C's `Succeed` and `Fail` labels remains on the
successful path.  Distinct temp/data block copies model `sortslice_memcpy`;
blocks moved within `data` use overlap-safe `SortSlice.memmove?`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Read one initialized logical entry from temporary merge storage. -/
def mergeLoTempRead? (storage : TempStorage κ ν) (index : Nat) :
    Option (SortSliceEntry κ ν) := do
  let cell ← storage.cells[index]?
  cell

/-- Initialize or replace one in-bounds logical temporary entry. -/
def mergeLoTempWrite? (storage : TempStorage κ ν) (index : Nat)
    (entry : SortSliceEntry κ ν) : Option (TempStorage κ ν) :=
  if h : index < storage.cells.size then
    some { storage with cells := storage.cells.set index (some entry) }
  else
    none

/-- Every cell in the indicated temporary range has been initialized.  This
is the precise precondition under which materializing that range is total. -/
def MergeLoTempRangeInitialized (storage : TempStorage κ ν)
    (source count : Nat) : Prop :=
  ∀ i, i < count →
    ∃ entry, mergeLoTempRead? storage (source + i) = some entry

/-- Copy a main-list range into the distinct temporary store.  This recursive
bulk-copy implementation itself requires a pinned call-site tag and a proof of
its physical direction, so there is no untagged memcpy-capable helper for an
evaluator call to bypass. -/
def mergeLoMemcpyDataToTemp?
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main }) :
    Nat → MergeState κ ν → Nat → Int → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, destination, source => do
      let entry ← state.data.read? source
      let storage ← mergeLoTempWrite? state.a destination entry
      mergeLoMemcpyDataToTemp? site hDirection count
        { state with a := storage } (destination + 1) (source + 1)

/-- Copy a temporary range into the main list.  As above, the recursive
implementation cannot be invoked without a tag proving the exact
temporary-to-main direction. -/
def mergeLoMemcpyTempToData?
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary }) :
    Nat → MergeState κ ν → Int → Nat → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, destination, source => do
      let entry ← mergeLoTempRead? state.a source
      let data ← state.data.write? destination entry
      mergeLoMemcpyTempToData? site hDirection count
        { state with data := data } (destination + 1) (source + 1)

/-- Materialize an initialized active part of the temporary run as a
`SortSlice`, so the shared `gallop_right` transcription can inspect it. -/
def mergeLoGatherTempEntries? :
    Nat → TempStorage κ ν → Nat → Array (SortSliceEntry κ ν) →
      Option (Array (SortSliceEntry κ ν))
  | 0, _, _, entries => some entries
  | count + 1, storage, source, entries => do
      let entry ← mergeLoTempRead? storage source
      mergeLoGatherTempEntries? count storage (source + 1) (entries.push entry)

/-- Materialize an initialized temporary range as the slice consumed by
`gallop_right`. -/
def mergeLoTempRun? (storage : TempStorage κ ν) (source count : Nat) :
    Option (SortSlice κ ν) := do
  let entries ← mergeLoGatherTempEntries? count storage source #[]
  pure { entries := entries }

end CPythonListsort
