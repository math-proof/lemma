import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  ∑ i, (x i + y i) = ∑ i, x i + ∑ i, y i := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  exact Finset.sum_add_distrib


@[path]
private lemma doit
  {x : ℕ → ℝ} :
-- imply
  ∑ i : Fin 3, x i = x 0 + x 1 + x 2 := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  exact Fin.sum_univ_three _


@[path]
private lemma pop
  {n : ℕ}
  {x : ℕ → ℝ} :
-- imply
  ∑ i < (n + 1), x i = ∑ i < n, x i + x n := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  exact Finset.sum_range_succ _ _


@[path]
private lemma shift
  {n : ℕ}
  {x : ℕ → ℝ} :
-- imply
  ∑ i < (n + 1), x i = ∑ i < n, x (i + 1) + x 0 := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  exact Finset.sum_range_succ' _ _


-- created on 2022-04-02
