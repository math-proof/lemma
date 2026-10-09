import Mathlib
import sympy.Basic


/--
[Pencil_norm_dotProduct_mul_sup_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Pencil_norm_dotProduct_mul_sup_le.lean)
-/
@[path]
private lemma main
  {r : ℕ}
  {a v w : Fin r → ℂ}
-- given
  (hav : ∑ i, a i * v i = 0) :
-- imply
  ‖∑ i, a i * w i‖ * (⨆ i, ‖v i‖)
      ≤ (∑ i, ‖a i‖) * ⨆ p : Fin r × Fin r, ‖v p.1 * w p.2 - v p.2 * w p.1‖ := by
-- proof
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · simp
  set S := ⨆ p : Fin r × Fin r, ‖v p.1 * w p.2 - v p.2 * w p.1‖ with hS_def
  have hS : ∀ p : Fin r × Fin r, ‖v p.1 * w p.2 - v p.2 * w p.1‖ ≤ S := fun p ↦
    le_ciSup (Finite.bddAbove_range fun p : Fin r × Fin r ↦ ‖v p.1 * w p.2 - v p.2 * w p.1‖) p
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i ↦ ‖v i‖
  have hsup : (⨆ i, ‖v i‖) = ‖v i₀‖ :=
    le_antisymm (ciSup_le hi₀) (le_ciSup (Finite.bddAbove_range fun i ↦ ‖v i‖) i₀)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS (i₀, i₀))
  have ha0 : 0 ≤ ∑ i, ‖a i‖ := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  rw [hsup]
  by_cases h0 : v i₀ = 0
  · rw [h0, norm_zero, mul_zero]; exact mul_nonneg ha0 hS0
  have key : v i₀ * ∑ i, a i * w i = ∑ i, a i * (v i₀ * w i - v i * w i₀) := by
    have h' : ∑ i, a i * (v i₀ * w i - v i * w i₀)
        = v i₀ * ∑ i, a i * w i - w i₀ * ∑ i, a i * v i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [h', hav, mul_zero, sub_zero]
  calc ‖∑ i, a i * w i‖ * ‖v i₀‖ = ‖v i₀ * ∑ i, a i * w i‖ := by rw [norm_mul, mul_comm]
    _ = ‖∑ i, a i * (v i₀ * w i - v i * w i₀)‖ := by rw [key]
    _ ≤ ∑ i, ‖a i * (v i₀ * w i - v i * w i₀)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖a i‖ * S := Finset.sum_le_sum fun i _ ↦ by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hS (i₀, i)) (norm_nonneg _)
    _ = (∑ i, ‖a i‖) * S := by rw [Finset.sum_mul]


-- created on 2026-10-05
