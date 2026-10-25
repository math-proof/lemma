/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Mathlib.Topology.UnitInterval
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part5


namespace StatMech.Universality

open Metric Set

open scoped unitInterval

noncomputable section

theorem closedBall_subset_finiteCenteredRadialGridStrictInterior
    (n : Nat) (mesh R : Real) (hmesh : 0 < mesh) (hR : 0 <= R)
    (hwide : 2 * R + 4 * mesh <= mesh * n) :
    closedBall (0 : Complex) R ⊆
      finiteCenteredRadialGridStrictInterior n mesh := by
  intro z hz
  have hnorm : norm z <= R := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have hrelo : -R <= z.re := by
    linarith [neg_le_of_abs_le (hre.trans hnorm)]
  have hrehi : z.re <= R := by
    linarith [le_of_abs_le (hre.trans hnorm)]
  have himlo : -R <= z.im := by
    linarith [neg_le_of_abs_le (him.trans hnorm)]
  have himhi : z.im <= R := by
    linarith [le_of_abs_le (him.trans hnorm)]
  have hq : 2 * R / mesh + 4 <= (n : Real) := by
    calc
      2 * R / mesh + 4 = (2 * R + 4 * mesh) / mesh := by
        field_simp [hmesh.ne']
      _ <= (mesh * (n : Real)) / mesh :=
        (div_le_div_iff_of_pos_right hmesh).mpr hwide
      _ = (n : Real) := by field_simp [hmesh.ne']
  have hsumlo : -2 * R / mesh <= (z.re + z.im) / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hsumhi : (z.re + z.im) / mesh <= 2 * R / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hdifflo : -2 * R / mesh <= (z.re - z.im) / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hdiffhi : (z.re - z.im) / mesh <= 2 * R / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hneg : -2 * R / mesh = -(2 * R / mesh) := by ring
  rw [hneg] at hsumlo hdifflo
  have hc1 : (isingCenteredRadialGridCoordinate mesh n z).1 =
      (n : Real) + (z.re + z.im) / mesh - 1 / 2 := by
    unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    field_simp [hmesh.ne']
    ring
  have hc2 : (isingCenteredRadialGridCoordinate mesh n z).2 =
      (n : Real) + (z.re - z.im) / mesh - 1 / 2 := by
    unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    field_simp [hmesh.ne']
    ring
  change 1 < (isingCenteredRadialGridCoordinate mesh n z).1 ∧
    (isingCenteredRadialGridCoordinate mesh n z).1 < (2 * n : Nat) - 2 ∧
    1 < (isingCenteredRadialGridCoordinate mesh n z).2 ∧
    (isingCenteredRadialGridCoordinate mesh n z).2 < (2 * n : Nat) - 2
  rw [hc1, hc2]
  constructor
  · linarith
  constructor
  · push_cast
    linarith
  constructor
  · linarith
  · push_cast
    linarith


end
end StatMech.Universality
