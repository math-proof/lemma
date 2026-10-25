/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/ListSortImpl.lean -/

import Def.CPythonListsort.Code.Transcription.Binarysort.Part3
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
import Theorem.CPythonListsort.Code.Transcription.FoundNewRun
import Theorem.CPythonListsort.Code.Transcription.MergeForceCollapse
import Def.CPythonListsort.Code.Transcription.MergeInitStorage
import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Def.CPythonListsort.Code.Transcription.ReverseSlice
import Def.CPythonListsort.Code.Transcription.ListSortImpl
/-!
# Snapshot-model `list_sort_impl`

This module assembles the version-one snapshot model of CPython's top-level
sort.  Keys and their optional payloads are already paired, the comparator is
pure and total, and allocator failure is excluded.  Within that boundary the
control flow retains initial/final reverse handling, natural-run discovery,
adaptive minrun extension, policy merges, the unconditional pending push,
final collapse, and temporary-storage cleanup.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

set_option linter.style.nativeDecide false in
/-- Small executable regression for run extension, stable forward order, and
the final temporary-storage cleanup. -/
example :
    (listSortImpl? (fun left right : Nat => decide (left < right))
      false true listSortExample).map
        (fun result =>
          (result.returnCode, result.fuelExhausted, result.state.a.backing,
            result.state.data.entries.toList)) =
      some
        (0, false, .inline,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 },
           { key := 2, value := some 21 },
           { key := 3, value := some 30 }]) := by
  decide

set_option linter.style.nativeDecide false in
/-- CPython's reverse-before/stable-sort/reverse-after pattern keeps equal-key
payloads in their original order while reversing the requested key order. -/
example :
    (listSortImpl? (fun left right : Nat => decide (left < right))
      true true listSortExample).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 3, value := some 30 },
           { key := 2, value := some 20 },
           { key := 2, value := some 21 },
           { key := 1, value := some 10 }]) := by
  decide

end CPythonListsort
