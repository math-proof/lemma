/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean -/

import Def.CPythonListsort.Code.Assembly.ListSortInputMode
import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Theorem.CPythonListsort.Code.Equivalence.MinrunResults.Part3
import Theorem.CPythonListsort.Code.Policy.PushRunPreservation
/-!
# Support lemmas for top-level listsort assembly

This module packages the initialized `MergeState`, the adaptive-minrun state
carried by the scan, and the frame facts for the small top-level transitions.
It deliberately does not define a second listsort evaluator: the traced
top-level assembly consumes the public helpers from the reviewed
`ListSortImpl` transcription.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-! ## Selected-platform word facts -/

/-- A source-admitted list length is represented exactly by the selected
64-bit word model. -/
theorem listSizeWord_toNat {size : Nat} (hsize : size ≤ PY_LIST_MAX) :
    (BitVec.ofNat 64 size : PySSize).toNat = size := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hsize ⊢
  omega

end CPythonListsort
