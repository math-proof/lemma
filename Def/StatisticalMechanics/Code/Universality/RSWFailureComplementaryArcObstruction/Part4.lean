/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part3
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

noncomputable def rlc_scaleTwoDoubleFailureGap :
    RlcAxisBarrierGap rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft where
  lower := -2
  upper := 0
  lower_mem := by
    rw [rlc_mem_axisHeights_iff,
      rlc_scaleTwoDoubleFailure_right_vertices]
    simp
  upper_mem := by
    rw [rlc_mem_axisHeights_iff,
      rlc_scaleTwoDoubleFailure_left_vertices]
    simp
  start_le := by
    simp [rlc_scaleTwoDoubleFailureRight, rlc_stdf_r0]
  lower_lt_upper := by omega
  upper_le_finish := by
    simp [rlc_scaleTwoDoubleFailureLeft, rlc_stdf_l6]
  interior_free := by
    intro t hlow hupp
    have ht : t = -1 := by omega
    subst t
    rw [rlc_axis_mem_connectorBarrier_iff,
      rlc_scaleTwoDoubleFailure_right_vertices,
      rlc_scaleTwoDoubleFailure_left_vertices]
    simp


def rlc_scaleTwoDoubleFailureOpenEdges : Finset (Sym2 (Site 2)) :=
  {s(![-3, -2], ![-2, -2]), s(![-3, -1], ![-2, -1]),
    s(![-1, -2], ![-1, -1]), s(![-1, -2], ![0, -2]),
    s(![0, -3], ![0, -2])}


def rlc_scaleTwoDoubleFailureConfig :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e ∈ rlc_scaleTwoDoubleFailureOpenEdges then true else false

end Universality
end StatMech
