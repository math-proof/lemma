/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part3


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem halfDiagonal_displacement_le_scale
    (z direction : Complex) (hdirection : ‖direction‖ <= 2)
    (scale : Real) (hscale : 0 <= scale) :
    dist z (z + ((scale / 2 : Real) : Complex) * direction) <= scale := by
  rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    scale / 2 * ‖direction‖ <= scale / 2 * 2 := by
      gcongr
    _ = scale := by ring

theorem norm_neg_one_add_I_le_two :
    ‖(-1 + Complex.I : Complex)‖ <= 2 := by
  calc
    ‖(-1 + Complex.I : Complex)‖ <= ‖(-1 : Complex)‖ + ‖Complex.I‖ :=
      norm_add_le _ _
    _ = 2 := by norm_num

theorem norm_one_add_I_le_two :
    ‖(1 + Complex.I : Complex)‖ <= 2 := by
  calc
    ‖(1 + Complex.I : Complex)‖ <= ‖(1 : Complex)‖ + ‖Complex.I‖ :=
      norm_add_le _ _
    _ = 2 := by norm_num

theorem norm_one_sub_I_le_two :
    ‖(1 - Complex.I : Complex)‖ <= 2 := by
  calc
    ‖(1 - Complex.I : Complex)‖ <= ‖(1 : Complex)‖ + ‖Complex.I‖ :=
      norm_sub_le _ _
    _ = 2 := by norm_num

theorem norm_neg_one_sub_I_le_two :
    ‖(-1 - Complex.I : Complex)‖ <= 2 := by
  calc
    ‖(-1 - Complex.I : Complex)‖ <= ‖(-1 : Complex)‖ + ‖Complex.I‖ :=
      norm_sub_le _ _
    _ = 2 := by norm_num


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
