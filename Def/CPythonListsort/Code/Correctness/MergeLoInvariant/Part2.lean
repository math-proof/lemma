/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeLoInvariant.lean -/

import Def.CPythonListsort.Code.Assembly.GallopCorrectness
import Structure.CPythonListsort.Code.Assembly.MergeLoSafety.Part4
import Structure.CPythonListsort.Code.Correctness.MergeSemanticPre
import Def.CPythonListsort.Code.Correctness.MergeMovementCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Correctness.StableMerge
import Abbrev.CPythonListsort.Code.Correctness.MergeLoInvariant
/-!
# Semantic invariant for `merge_lo`

The reviewed safety invariant describes cursor geometry and storage validity.
This separate correctness invariant fixes immutable snapshots of the two
trimmed input runs and relates the emitted prefix, the live temporary suffix,
and the live main-data suffix to one shared stable-merge target.  Keeping this
layer separate prevents correctness-only order hypotheses from leaking into
the arbitrary-comparator safety theorem.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Number of entries already emitted by a live forward cursor. -/
def mergeLoEmittedCount (call : MergeAtCall (Occurrence alpha) nu)
    (machine : MergeLoMachine (Occurrence alpha) nu) : Nat :=
  call.na + call.nb - (machine.na + machine.nb)

/-- Entries already emitted at the beginning of the affected main range. -/
def mergeLoEmittedEntries (call : MergeAtCall (Occurrence alpha) nu)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries machine.state.data call.ssa.toNat
    (mergeLoEmittedCount call machine)).toList

/-- Exact logical contents of the active temporary A suffix. -/
def MergeLoTempSuffixMatches
    (storage : TempStorage (Occurrence alpha) nu)
    (left : List (SortSliceEntry (Occurrence alpha) nu))
    (source count : Nat) : Prop :=
  source + count ≤ left.length ∧
    ∀ i, i < count →
      mergeLoTempRead? storage (source + i) = left[source + i]?

/-- Exact logical contents of the active main-data B suffix. -/
def MergeLoMainSuffixMatches
    (data : SortSlice (Occurrence alpha) nu)
    (right : List (SortSliceEntry (Occurrence alpha) nu))
    (source : Int) (consumed count : Nat) : Prop :=
  consumed + count ≤ right.length ∧
    ∀ i, i < count →
      data.read? (source + Int.ofNat i) = right[consumed + i]?

end CPythonListsort
