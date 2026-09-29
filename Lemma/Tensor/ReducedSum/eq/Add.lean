import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  ∑ i, (x i + y i) = ∑ i, x i + ∑ i, y i := by
-- proof
  exact Finset.sum_add_distrib


@[main]
private lemma doit
  {x : ℕ → ℝ} :
-- imply
  ∑ i : Fin 3, x i = x 0 + x 1 + x 2 := by
-- proof
  exact Fin.sum_univ_three _


@[main]
private lemma pop
  {n : ℕ}
  {x : ℕ → ℝ} :
-- imply
  ∑ i ∈ Finset.range (n + 1), x i = ∑ i ∈ Finset.range n, x i + x n := by
-- proof
  exact Finset.sum_range_succ _ _


@[main]
private lemma shift
  {n : ℕ}
  {x : ℕ → ℝ} :
-- imply
  ∑ i ∈ Finset.range (n + 1), x i = ∑ i ∈ Finset.range n, x (i + 1) + x 0 := by
-- proof
  exact Finset.sum_range_succ' _ _


-- created on 2026-09-27
