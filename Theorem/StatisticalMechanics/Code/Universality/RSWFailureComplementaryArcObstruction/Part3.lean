/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
import Def.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part3
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

@[simp]
theorem rlc_scaleTwoDoubleFailure_right_vertices :
    rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1 =
      {![0, -2], ![1, -2], ![1, -1], ![2, -1], ![3, -1],
        ![4, -1], ![4, 0]} := by
  simp [rlc_scaleTwoDoubleFailureRight, rlc_pathVertices,
    rlc_stdf_rightWalk, rlc_stdf_r0, rlc_stdf_r1, rlc_stdf_r2,
    rlc_stdf_r3, rlc_stdf_r4, rlc_stdf_r5, rlc_stdf_r6,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

@[simp]
theorem rlc_scaleTwoDoubleFailure_left_vertices :
    rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1 =
      {![-4, -2], ![-3, -2], ![-2, -2], ![-2, -1], ![-2, 0],
        ![-1, 0], ![0, 0]} := by
  simp [rlc_scaleTwoDoubleFailureLeft, rlc_pathVertices,
    rlc_stdf_leftWalk, rlc_stdf_l0, rlc_stdf_l1, rlc_stdf_l2,
    rlc_stdf_l3, rlc_stdf_l4, rlc_stdf_l5, rlc_stdf_l6,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

@[simp]
theorem rlc_scaleTwoDoubleFailure_right_edges :
    rlc_pathEdges rlc_scaleTwoDoubleFailureRight.1 =
      {s(![0, -2], ![1, -2]), s(![1, -2], ![1, -1]),
        s(![1, -1], ![2, -1]), s(![2, -1], ![3, -1]),
        s(![3, -1], ![4, -1]), s(![4, -1], ![4, 0])} := by
  simp [rlc_scaleTwoDoubleFailureRight, rlc_pathEdges,
    rlc_stdf_rightWalk, rlc_stdf_r0, rlc_stdf_r1, rlc_stdf_r2,
    rlc_stdf_r3, rlc_stdf_r4, rlc_stdf_r5, rlc_stdf_r6,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

@[simp]
theorem rlc_scaleTwoDoubleFailure_left_edges :
    rlc_pathEdges rlc_scaleTwoDoubleFailureLeft.1 =
      {s(![-4, -2], ![-3, -2]), s(![-3, -2], ![-2, -2]),
        s(![-2, -2], ![-2, -1]), s(![-2, -1], ![-2, 0]),
        s(![-2, 0], ![-1, 0]), s(![-1, 0], ![0, 0])} := by
  simp [rlc_scaleTwoDoubleFailureLeft, rlc_pathEdges,
    rlc_stdf_leftWalk, rlc_stdf_l0, rlc_stdf_l1, rlc_stdf_l2,
    rlc_stdf_l3, rlc_stdf_l4, rlc_stdf_l5, rlc_stdf_l6,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]


end Universality
end StatMech
