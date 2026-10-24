/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Schnirelmann.lean -/


import sympy.atlas.Combinatorics.Schnirelmann
import Lemma.Finset.Schnirelmann
import Mathlib.Tactic


namespace MathlibExtTest.Combinatorics.Schnirelmann

open Finset
open scoped Pointwise

-- Two dense sets containing zero have a sumset that is an additive basis.
example {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ A + B)] (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (hA : (2 : ℝ)⁻¹ ≤ schnirelmannDensity A)
    (hB : (2 : ℝ)⁻¹ ≤ schnirelmannDensity B) :
    ∃ h : ℕ, ∀ n : ℕ, ∃ x : Fin h → ℕ,
      (∀ i, x i ∈ A + B) ∧ n = ∑ i, x i := by
  have hsum := schnirelmannDensity_add_lower_bound hA0 hB0
  have hB_le : schnirelmannDensity B ≤ 1 := schnirelmannDensity_le_one
  have hprod : 0 ≤ (schnirelmannDensity A - (2 : ℝ)⁻¹) *
      (1 - schnirelmannDensity B) :=
    mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB_le)
  have hσ : (4 : ℝ)⁻¹ * 3 ≤ schnirelmannDensity (A + B) := by
    norm_num at hA hB hprod ⊢
    nlinarith
  have hzero : 0 ∈ A + B := Set.mem_add.mpr ⟨0, hA0, 0, hB0, by simp⟩
  apply exists_additive_basis_of_pos_schnirelmannDensity hzero
  exact (by norm_num : (0 : ℝ) < (4 : ℝ)⁻¹ * 3).trans_le hσ

end MathlibExtTest.Combinatorics.Schnirelmann
