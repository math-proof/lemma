/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

def rlc_stdf_leftWalk :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Walk
      rlc_stdf_l0 rlc_stdf_l6 :=
  .cons rlc_stdf_ladj01
    (.cons rlc_stdf_ladj12
      (.cons rlc_stdf_ladj23
        (.cons rlc_stdf_ladj34
          (.cons rlc_stdf_ladj45
            (.cons rlc_stdf_ladj56 .nil)))))


noncomputable def rlc_scaleTwoDoubleFailureLeft :
    RlcLeftDiagonalPath 2 := by
  let x : leftSide (-4) 0 (-2) 2 :=
    ⟨(rlc_stdf_l0 : Site 2), by
      simp [rlc_stdf_l0, mem_leftSide, mem_rect]⟩
  let y : rightSide (-4) 0 (-2) 2 :=
    ⟨(rlc_stdf_l6 : Site 2), by
      simp [rlc_stdf_l6, mem_rightSide, mem_rect]⟩
  let p : RlcCrossingPath (-4) 0 (-2) 2 :=
    ⟨x, y, rlc_stdf_leftWalk.toPath⟩
  exact ⟨p, by simp [p, x, rlc_stdf_l0, rlc_lowerHalf],
    by simp [p, y, rlc_stdf_l6, rlc_upperHalf]⟩

end Universality
end StatMech
