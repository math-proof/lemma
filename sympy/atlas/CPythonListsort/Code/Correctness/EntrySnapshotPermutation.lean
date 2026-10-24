/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/EntrySnapshotPermutation.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.ScanRemainder

/-!
# Persistent whole-entry input snapshot

The scan invariant needs more than a key-only suffix snapshot: every movement
step must keep the original key occurrence paired with its original optional
payload.  `EntrySnapshotPermutation` records that persistent whole-array fact.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- The current slice contains exactly the absolutely tagged source entries,
including their optional payloads.  This invariant deliberately ranges over
the whole array, so local correctness posts can preserve it by a frame plus a
whole-entry permutation of the modified range. -/
def EntrySnapshotPermutation (source : SortSlice κ ν)
    (current : SortSlice (Occurrence κ) ν) : Prop :=
  current.entries.toList.Perm
    (tagSortSliceOccurrences source).entries.toList

namespace EntrySnapshotPermutation

private def wrongPayloadKeyedInput : ListSortInput Nat Nat :=
  ListSortInput.keyed #[(1, 10), (2, 20)]

private def wrongPayloadTaggedSlice : SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[{ key := { value := 1, origin := 0 }, value := some 10 },
        { key := { value := 2, origin := 1 }, value := some 99 }] }
