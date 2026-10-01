import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {n i j : ℕ}
  {L : ℕ → ℕ → ℂ}
-- given
  (h₀ : ∀ i j, j > i → L i j = 0)
  (h₁ : i < n) :
-- imply
  ∑ k ∈ Finset.range n, L i k * ~(L j k) = ∑ k ∈ Finset.range (min i j + 1), L i k * ~(L j k) := by
-- proof
  rw [← Finset.sum_range_add_sum_Ico _ (show min i j + 1 ≤ n by omega)]
  have h₂ : ∑ k ∈ Finset.Ico (min i j + 1) n, L i k * ~(L j k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' := (Finset.mem_Ico.mp hk).1
    rcases le_total i j with hij | hij
    ·
      rw [min_eq_left hij] at hk'
      simp [h₀ i k (by omega)]
    ·
      rw [min_eq_right hij] at hk'
      simp [h₀ j k (by omega)]
  rw [h₂, add_zero]


-- created on 2026-09-27
