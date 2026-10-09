import Mathlib
import sympy.Basic


/--
[Pencil_norm_minor_le_two_mul_sup_minor_row](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Pencil_norm_minor_le_two_mul_sup_minor_row.lean)
-/
@[path]
private lemma main
  {r : ℕ}
  {v w : Fin r → ℂ}
  {i₀ : Fin r}
  {i j : Fin r}
-- given
  (hi₀ : ∀ i, ‖v i‖ ≤ ‖v i₀‖) :
-- imply
  ‖v i * w j - v j * w i‖ ≤ 2 * ⨆ l, ‖v i₀ * w l - v l * w i₀‖ := by
-- proof
  set M := ⨆ l, ‖v i₀ * w l - v l * w i₀‖ with hM
  have hle : ∀ l, ‖v i₀ * w l - v l * w i₀‖ ≤ M := fun l ↦
    le_ciSup (Finite.bddAbove_range fun l ↦ ‖v i₀ * w l - v l * w i₀‖) l
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hle i₀)
  by_cases h0 : v i₀ = 0
  · have hv : ∀ k, v k = 0 := fun k ↦ by
      have hk := hi₀ k
      rw [h0, norm_zero] at hk
      exact norm_eq_zero.mp (le_antisymm hk (norm_nonneg _))
    have hz : v i * w j - v j * w i = 0 := by rw [hv i, hv j]; ring
    rw [hz, norm_zero]
    linarith
  · have hpos : 0 < ‖v i₀‖ := norm_pos_iff.mpr h0
    have key : v i₀ * (v i * w j - v j * w i)
        = v i * (v i₀ * w j - v j * w i₀) - v j * (v i₀ * w i - v i * w i₀) := by ring
    have h1 : ‖v i₀‖ * ‖v i * w j - v j * w i‖ ≤ ‖v i₀‖ * M + ‖v i₀‖ * M := by
      rw [← norm_mul, key]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul (hi₀ i) (hle j) (norm_nonneg _) (norm_nonneg _)
      · rw [norm_mul]; exact mul_le_mul (hi₀ j) (hle i) (norm_nonneg _) (norm_nonneg _)
    rw [← mul_add] at h1
    have h2 : ‖v i * w j - v j * w i‖ ≤ M + M := le_of_mul_le_mul_left h1 hpos
    linarith


-- created on 2026-10-05
