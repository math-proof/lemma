/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_rca_leftWalk :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Walk
      (rlc_rca_lv 0) (rlc_rca_lv 10) :=
  .cons (rlc_rca_ladj 0)
    (.cons (rlc_rca_ladj 1)
      (.cons (rlc_rca_ladj 2)
        (.cons (rlc_rca_ladj 3)
          (.cons (rlc_rca_ladj 4)
            (.cons (rlc_rca_ladj 5)
              (.cons (rlc_rca_ladj 6)
                (.cons (rlc_rca_ladj 7)
                  (.cons (rlc_rca_ladj 8)
                    (.cons (rlc_rca_ladj 9) .nil)))))))))


def rlc_retainedChoiceAuditLeft : RlcLeftDiagonalPath 2 := by
  let x : leftSide (-4) 0 (-2) 2 :=
    ⟨(rlc_rca_lv 0 : Site 2), by
      simp [rlc_rca_lv, mem_leftSide, mem_rect]⟩
  let y : rightSide (-4) 0 (-2) 2 :=
    ⟨(rlc_rca_lv 10 : Site 2), by
      simp [rlc_rca_lv, mem_rightSide, mem_rect]⟩
  let p : RlcCrossingPath (-4) 0 (-2) 2 :=
    ⟨x, y, rlc_rca_leftWalk.toPath⟩
  exact ⟨p, by simp [p, x, rlc_rca_lv, rlc_lowerHalf],
    by simp [p, y, rlc_rca_lv, rlc_upperHalf]⟩

end
end StatMech.Universality
