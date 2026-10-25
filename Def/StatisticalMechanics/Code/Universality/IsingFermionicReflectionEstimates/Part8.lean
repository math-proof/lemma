/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part3


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

def survivalExceptionalPointwiseProjection
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target →
      IsingLineChoicePathFamily (R - level) walkLength
          (rightGapNeighbor R level hgap) (rightGapLeft R level) ×
        VerticalChoicePathFamily walkLength start.2 target.2 := fun w =>
  let path := w.1.1.1.reflectPrefix.steps
  ⟨⟨horizontalRightCode path, by
      simpa [horizontalRightCode, path, reflectPrefix_length] using
        w.1.1.2.2.2.1,
      survivalExceptional_horizontal_run_left R level walkLength start target
        hstart hlevel hgap w⟩,
    ⟨verticalCode path, by
      simpa [verticalCode, path, reflectPrefix_length] using
        w.1.1.2.2.2.1,
      reflectPrefix_verticalCode_endpoint w.1.1⟩⟩

end IsingDiagonalWalkHitSplit
end StatMech.Universality
