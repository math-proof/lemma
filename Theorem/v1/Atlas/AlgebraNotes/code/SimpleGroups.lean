/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SimpleGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraNotes.code.SimpleGroups.Part2


namespace SimpleGroups

open Matrix

section OneParamSubgroupTheorem

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma diagRotation_add (θ₁ θ₂ : ℝ) :
    diagRotation θ₁ * diagRotation θ₂ = diagRotation (θ₁ + θ₂) := by
  simp only [diagRotation]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
  · ring_nf
  · ring_nf

lemma diagRotation_zero : diagRotation 0 = 1 := by
  simp only [diagRotation]
  ext i j; fin_cases i <;> fin_cases j <;> simp

set_option maxHeartbeats 800000 in
lemma diagRotation_mem_SU2 (θ : ℝ) : diagRotation θ ∈ SU2 := by
  simp only [diagRotation, Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
  have hconj1 : starRingEnd ℂ (Complex.exp (↑θ * Complex.I)) =
      Complex.exp (-(↑θ * Complex.I)) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, Complex.conj_I]
  have hconj2 : starRingEnd ℂ (Complex.exp (-(↑θ * Complex.I))) =
      Complex.exp (↑θ * Complex.I) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, Complex.conj_I]
  have hconj_struct : ∀ z : ℂ, ({ re := z.re, im := -z.im } : ℂ) = starRingEnd ℂ z := by
    intro z; apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          mul_zero, add_zero, zero_add, Matrix.one_apply,
          Fin.isValue, ite_true, ite_false, Fin.reduceFinMk, Fin.reduceEq,
          Matrix.transpose_apply]
    · rw [hconj_struct, hconj1, ← Complex.exp_add]; simp
    · apply Complex.ext <;> simp
    · apply Complex.ext <;> simp
    · rw [hconj_struct, hconj2, ← Complex.exp_add]; simp
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          zero_mul, add_zero, zero_add, Matrix.one_apply,
          Fin.isValue, ite_true, ite_false, Fin.reduceFinMk, Fin.reduceEq,
          Matrix.transpose_apply]
    · rw [hconj_struct, hconj1, ← Complex.exp_add]; simp
    · apply Complex.ext <;> simp
    · apply Complex.ext <;> simp
    · rw [hconj_struct, hconj2, ← Complex.exp_add]; simp
  · simp [Matrix.det_fin_two, ← Complex.exp_add]

end OneParamSubgroupTheorem
end SimpleGroups
