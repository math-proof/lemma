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
      (Nat.multinomial Finset.univ k : ℂ) * ∏ i, x i ^ k i := by
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


-- created on 2023-08-20
