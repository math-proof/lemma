/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean -/

import Def.CPythonListsort.Code.Correctness.ScanStepCorrectness.Part3
import Def.CPythonListsort.Code.Correctness.MergeForceCollapseCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part2
/-!
# Equivariance under mirrored occurrence origins

Reverse-mode correctness compares the actual initially reversed execution,
whose carried origins run backwards, with a canonical execution over the
reversed source.  This file supplies the explicit relabeling and proves that
the implementation observes only occurrence values: changing every origin by
the same mirror map commutes with the data-moving evaluator.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

@[simp] theorem mirrorReverseEqualResult_slice (size : Nat)
    (result : ReverseEqualResult (Occurrence alpha) nu) :
    (mirrorReverseEqualResult size result).slice = mirrorSortSlice size result.slice := rfl

@[simp] theorem mirrorReverseEqualResult_fuel (size : Nat)
    (result : ReverseEqualResult (Occurrence alpha) nu) :
    (mirrorReverseEqualResult size result).fuelExhausted = result.fuelExhausted := rfl

end CPythonListsort
