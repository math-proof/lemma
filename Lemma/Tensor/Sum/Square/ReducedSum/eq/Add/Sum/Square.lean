import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (hn : n > 0) :
-- imply
  ∑ i : Fin n, (x i - (∑ j : Fin n, x j) / n) ^ 2 = ∑ i : Fin n, x i ^ 2 - (∑ j : Fin n, x j) ^ 2 / n := by
-- proof
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : ∀ c : ℝ, ∑ i : Fin n, (x i - c) ^ 2 = ∑ i : Fin n, x i ^ 2 - 2 * c * ∑ i : Fin n, x i + n * c ^ 2 := by
    intro c
    have e : ∀ i : Fin n, (x i - c) ^ 2 = x i ^ 2 - 2 * c * x i + c ^ 2 := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [key]
  field_simp
  ring


-- created on 2023-10-08
