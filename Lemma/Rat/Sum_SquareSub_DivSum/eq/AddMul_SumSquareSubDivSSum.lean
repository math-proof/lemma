import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {m n : ℕ}
  {x : ℕ → ℕ → ℝ}
-- given
  (hn : n > 0) :
-- imply
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, (x i j - (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, x i j) / (m * n)) ^ 2 =
      n * ∑ i ∈ Finset.range m, ((∑ j ∈ Finset.range n, x i j) / n - (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, x i j) / (m * n)) ^ 2 +
        ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, (x i j - (∑ j ∈ Finset.range n, x i j) / n) ^ 2 := by
-- proof
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have row : ∀ (y : ℕ → ℝ) (c : ℝ), ∑ j ∈ Finset.range n, (y j - c) ^ 2 =
      n * ((∑ j ∈ Finset.range n, y j) / n - c) ^ 2 + ∑ j ∈ Finset.range n, (y j - (∑ j ∈ Finset.range n, y j) / n) ^ 2 := by
    intro y c
    have key : ∀ d : ℝ, ∑ j ∈ Finset.range n, (y j - d) ^ 2 = ∑ j ∈ Finset.range n, y j ^ 2 - 2 * d * ∑ j ∈ Finset.range n, y j + n * d ^ 2 := by
      intro d
      have e : ∀ j, (y j - d) ^ 2 = y j ^ 2 - 2 * d * y j + d ^ 2 := fun j => by ring
      rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [key c, key]
    field_simp
    ring
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact row (x i) _


-- created on 2020-03-27
