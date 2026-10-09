import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.Pi
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n m : ℕ}
  {x : Fin n → ℂ} :
-- imply
  (∑ i, x i) ^ m = ∑ k ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (m + 1)).filter (fun k => ∑ i, k i = m),
      (m.factorial : ℂ) / (∏ i, ((k i).factorial : ℂ)) * ∏ i, x i ^ k i := by
-- proof
  have hs : Finset.piAntidiag Finset.univ m = (Fintype.piFinset fun _ : Fin n => Finset.range (m + 1)).filter (fun k => ∑ i, k i = m) := by
    ext k
    simp only [Finset.mem_piAntidiag, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Finset.mem_univ, implies_true,
      and_true]
    constructor
    · intro h
      refine ⟨fun i => ?_, h⟩
      have := Finset.single_le_sum (f := k) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      exact Nat.lt_succ_of_le (this.trans h.le)
    · exact fun h => h.2
  rw [Finset.sum_pow_eq_sum_piAntidiag, hs]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hspec := Nat.multinomial_spec Finset.univ k
  rw [(Finset.mem_filter.mp hk).2] at hspec
  have hne : (∏ i, ((k i).factorial : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [eq_div_iff hne, mul_comm]
  exact_mod_cast hspec


-- created on 2023-08-20
