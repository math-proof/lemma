import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.Basic


@[path]
private lemma main
  {r : Fin 12 → ℝ}
-- given
  (h₀ : ∀ i, 0 < r i)
  (h₁ : ∀ i j, r i = r j)
  (h₂ : ∏ i, r i = 1 / 2) :
-- imply
  r 0 = (1 / 2) ^ (1 / 12 : ℝ) ∧
    r 0 * r 1 = ((1 / 2) ^ (1 / 12 : ℝ)) ^ 2 ∧
    r 0 * r 1 * r 2 * r 3 * r 4 = ((1 / 2) ^ (1 / 12 : ℝ)) ^ 5 := by
-- proof
  have hr : ∀ i, r i = r 0 := fun i => h₁ i 0
  have hpos : 0 < r 0 := h₀ 0
  have hprod : r 0 ^ 12 = 1 / 2 := by
    rw [← h₂, Finset.prod_congr rfl (fun i _ => hr i), Finset.prod_const, Finset.card_univ]
    simp
  have hroot : r 0 = (r 0 ^ 12) ^ (1 / 12 : ℝ) := by
    rw [← Real.rpow_natCast (r 0) 12, ← Real.rpow_mul hpos.le]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hroot, hprod]
  ·
    rw [hr 1, hroot, hprod]
    ring
  ·
    rw [hr 1, hr 2, hr 3, hr 4, hroot, hprod]
    ring


-- created on 2026-10-11
-- updated on 2026-10-17
