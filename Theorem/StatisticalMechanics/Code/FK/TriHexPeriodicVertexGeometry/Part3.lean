/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part3
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


@[simp] theorem triangularPlaneVertex_apply (z : Site 2) :
    triangularPlaneVertex z = triHexPlanePeriod z := rfl

@[simp] theorem triangularPlaneVertex_shift (z x : Site 2) :
    triangularPlaneVertex (triangular.shift z x) =
      triangularPlaneVertex x + triHexPlanePeriod z := by
  change triHexPlanePeriod (x + z) =
    triHexPlanePeriod x + triHexPlanePeriod z
  exact map_add triHexPlanePeriod x z


theorem triHexPlanePeriod_bounded_finite (R : Real) :
    {z : Site 2 | ‖triHexPlanePeriod z‖ <= R}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt R
  apply (Set.Finite.pi (fun _ : Fin 2 =>
    Set.finite_Icc (-(N : Int)) (N : Int))).subset
  intro z hz
  rw [Set.mem_pi]
  intro i _hi
  have habs : |(z i : Real)| <= ‖triHexPlanePeriod z‖ := by
    fin_cases i
    · simpa using Complex.abs_re_le_norm (triHexPlanePeriod z)
    · simpa using Complex.abs_im_le_norm (triHexPlanePeriod z)
  have hlt : |(z i : Real)| < N := habs.trans_lt (hz.trans_lt hN)
  rw [abs_lt] at hlt
  constructor
  · exact_mod_cast hlt.1.le
  · exact_mod_cast hlt.2.le

theorem triangularPlaneVertex_bounded_finite (R : Real) :
    {z : Site 2 | ‖(triangularPlaneVertex z : Complex)‖ <= R}.Finite := by
  simpa using triHexPlanePeriod_bounded_finite R


end StatMech.FK.PeriodicPlanar
