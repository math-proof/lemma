import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {n i j : ℕ}
  {L : ℕ → ℕ → ℂ}
-- given
  (h : ∀ i j, j > i → L i j = 0) :
-- imply
  ∑ k ∈ Finset.Ico (min i j + 1) n, L i k * ~(L j k) = 0 := by
-- proof
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' := (Finset.mem_Ico.mp hk).1
  rcases le_total i j with hij | hij
  ·
    rw [min_eq_left hij] at hk'
    simp [h i k (by omega)]
  ·
    rw [min_eq_right hij] at hk'
    simp [h j k (by omega)]


-- created on 2023-06-23
