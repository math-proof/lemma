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
import Def.StatisticalMechanics.Code.Onsager.KWSpectralSharp.Part2


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


theorem ons_arrivalTurnMatrix_isHermitian (L : ℕ) :
    (ons_arrivalTurnMatrix L).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext ⟨p2, nu⟩ ⟨p1, mu⟩
  simp only [Matrix.conjTranspose_apply]
  by_cases h : p1 = p2
  · subst p2
    fin_cases mu <;> fin_cases nu <;>
      simp [ons_arrivalTurnMatrix, ons_turnMatrix, ons_turnW, ons_turnRoot_conj]
  · simp [ons_arrivalTurnMatrix, h, Ne.symm h]

theorem ons_arrivalTurnMatrix_centered_apply (L : ℕ) (d2 d1 : ons_Dart L) :
    (ons_arrivalTurnMatrix L - 1) d2 d1 =
      if d2.1 = d1.1 then
        (ons_turnMatrix ons_turnRoot - 1) d2.2 d1.2 else 0 := by
  by_cases hsite : d2.1 = d1.1
  · simp [ons_arrivalTurnMatrix, Matrix.one_apply, hsite, Prod.ext_iff]
  · have hdart : d2 ≠ d1 := fun h => hsite (congrArg Prod.fst h)
    simp [ons_arrivalTurnMatrix, hsite, hdart]

theorem ons_arrivalTurnMatrix_centered_sq (L : ℕ) [NeZero L] :
    (ons_arrivalTurnMatrix L - 1) * (ons_arrivalTurnMatrix L - 1) =
      (2 : ℂ) • (1 : Matrix (ons_Dart L) (ons_Dart L) ℂ) := by
  ext ⟨⟨x2, y2⟩, nu⟩ ⟨⟨x1, y1⟩, mu⟩
  simp only [Matrix.mul_apply, ons_arrivalTurnMatrix_centered_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x2]
  · rw [Finset.sum_eq_single y2]
    · have hlocal := congrFun (congrFun ons_turnMatrix_centered_sq nu) mu
      by_cases hsite : (x2, y2) = (x1, y1)
      · cases hsite
        simpa [Matrix.mul_apply, Matrix.one_apply] using hlocal
      · have hdart : ((x2, y2), nu) ≠ ((x1, y1), mu) :=
          fun h => hsite (congrArg Prod.fst h)
        simp [hsite, hdart]
    · intro y _ hy
      have hy' : y2 ≠ y := Ne.symm hy
      simp [hy']
    · simp
  · intro x _ hx
    have hx' : x2 ≠ x := Ne.symm hx
    simp [hx']
  · simp


end StatMech.Onsager
