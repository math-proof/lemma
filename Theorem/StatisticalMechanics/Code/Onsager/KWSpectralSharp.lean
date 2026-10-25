/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Def.StatisticalMechanics.Code.Onsager.KWSpectralSharp


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


theorem ons_turnRoot_conj : star ons_turnRoot = ons_turnRoot⁻¹ := by
  simpa only [RCLike.star_def] using
    (Complex.inv_eq_conj (norm_ons_turnRoot)).symm

theorem ons_turnRoot_ne_zero : ons_turnRoot ≠ 0 := by
  intro h
  have := ons_turnRoot_sq
  simp [h] at this
  exact Complex.I_ne_zero this.symm

theorem ons_turnMatrix_turnRoot_isHermitian :
    (ons_turnMatrix ons_turnRoot).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext mu nu
  fin_cases mu <;> fin_cases nu <;>
    simp [ons_turnMatrix, ons_turnW, ons_turnRoot_conj]


theorem ons_turnMatrix_centered_sq :
    (ons_turnMatrix ons_turnRoot - 1) * (ons_turnMatrix ons_turnRoot - 1) =
      (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext mu nu
  fin_cases mu <;> fin_cases nu <;>
    simp [ons_turnMatrix, ons_turnW, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_four, ons_turnRoot_ne_zero] <;>
    ring_nf <;>
    simp [ons_turnRoot_sq]


end StatMech.Onsager
