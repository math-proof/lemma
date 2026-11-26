import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
import Notation.Algebra.Power


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (hn : n > 0) :
-- imply
  ∑ i < n, (x i - (∑ j < n, x j) / n)² = (∑ i < n, ∑ j < i, (x i - x j)²) / n := by
-- proof
  simp only [Nat.Iio_eq_range]
  have e1 : ∀ (m : ℕ) (a : ℝ), (Finset.range m).sum (fun j => (a - x j)²) = m * a² - 2 * a * (Finset.range m).sum x + (Finset.range m).sum (fun j => x j ^ 2) := by
    intro m a
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [Finset.sum_range_succ]
      rw [ih]
      push_cast
      ring
  have e2 : ∀ (m : ℕ) (a : ℝ), (Finset.range m).sum (fun j => (x j - a)²) = m * a² - 2 * a * (Finset.range m).sum x + (Finset.range m).sum (fun j => x j ^ 2) := by
    intro m a
    rw [← e1]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have key : ∀ m : ℕ, (Finset.range m).sum (fun i => (Finset.range i).sum (fun j => (x i - x j)²)) = m * (Finset.range m).sum (fun i => x i ^ 2) - ((Finset.range m).sum (fun i => x i))² := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [Finset.sum_range_succ]
      rw [ih, e1]
      push_cast
      ring
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [e2, key]
  field_simp
  ring


-- created on 2019-11-15
-- updated on 2026-11-26
