/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_rca_rightWalk :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Walk
      (rlc_rca_rv 0) (rlc_rca_rv 9) :=
  .cons (rlc_rca_radj 0)
    (.cons (rlc_rca_radj 1)
      (.cons (rlc_rca_radj 2)
        (.cons (rlc_rca_radj 3)
          (.cons (rlc_rca_radj 4)
            (.cons (rlc_rca_radj 5)
              (.cons (rlc_rca_radj 6)
                (.cons (rlc_rca_radj 7)
                  (.cons (rlc_rca_radj 8) .nil))))))))


def rlc_retainedChoiceAuditRight : RlcRightDiagonalPath 2 := by
  let x : leftSide 0 4 (-2) 2 :=
    ⟨(rlc_rca_rv 0 : Site 2), by
      simp [rlc_rca_rv, mem_leftSide, mem_rect]⟩
  let y : rightSide 0 4 (-2) 2 :=
    ⟨(rlc_rca_rv 9 : Site 2), by
      simp [rlc_rca_rv, mem_rightSide, mem_rect]⟩
  let p : RlcCrossingPath 0 4 (-2) 2 :=
    ⟨x, y, rlc_rca_rightWalk.toPath⟩
  exact ⟨p, by simp [p, x, rlc_rca_rv, rlc_lowerHalf],
    by simp [p, y, rlc_rca_rv, rlc_upperHalf]⟩

def rlc_rca_lv : Fin 11 → rect (-4) 0 (-2) 2
  | 0 => ⟨![-4, -2], by simp [mem_rect]⟩
  | 1 => ⟨![-3, -2], by simp [mem_rect]⟩
  | 2 => ⟨![-2, -2], by simp [mem_rect]⟩
  | 3 => ⟨![-1, -2], by simp [mem_rect]⟩
  | 4 => ⟨![-1, -1], by simp [mem_rect]⟩
  | 5 => ⟨![-1, 0], by simp [mem_rect]⟩
  | 6 => ⟨![-1, 1], by simp [mem_rect]⟩
  | 7 => ⟨![-2, 1], by simp [mem_rect]⟩
  | 8 => ⟨![-2, 2], by simp [mem_rect]⟩
  | 9 => ⟨![-1, 2], by simp [mem_rect]⟩
  | 10 => ⟨![0, 2], by simp [mem_rect]⟩

end
end StatMech.Universality
