/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean -/

import Def.CPythonListsort.Code.Correctness.ScanStepCorrectness.Part3
import Def.CPythonListsort.Code.Correctness.MergeForceCollapseCorrectness.Part2
import Theorem.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part2
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

def mirrorDescendingScanResult (size : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) :
    DescendingScanResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

end CPythonListsort
