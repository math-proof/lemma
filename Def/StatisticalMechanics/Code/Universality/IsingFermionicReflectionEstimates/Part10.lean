/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part10


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

def survivalExceptionalMirrorProjection
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level) :
    SurvivalExceptionalMirrorFamily R start (level : Int) walkLength target →
      IsingLineChoicePathFamily level walkLength
          (leftGapNeighbor level hlevel) (leftGapLeft level) ×
        {v : List Bool // v.length = walkLength} := fun w =>
  let path := w.1.1.1.reflectPrefix.steps
  ⟨⟨horizontalLeftCode path, by
      simpa [horizontalLeftCode, path, reflectPrefix_length] using
        w.1.1.2.2.2.1,
      survivalExceptionalMirror_horizontal_run_left R level walkLength
        start target hstart hlevel w⟩,
    ⟨verticalCode path, by
      simpa [verticalCode, path, reflectPrefix_length] using
        w.1.1.2.2.2.1⟩⟩

end IsingDiagonalWalkHitSplit
end StatMech.Universality
