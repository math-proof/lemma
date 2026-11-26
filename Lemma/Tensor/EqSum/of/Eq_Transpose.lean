import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {A : ℕ → ℕ → ℂ}
-- given
  (h : ∀ i j, A i j = A j i) :
-- imply
  ∑ i < n, ∑ j < n, A i j =
    ∑ i < n, A i i + 2 * ∑ i < n, ∑ j < i, A i j := by
-- proof
  simp only [Nat.Iio_eq_range]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hs : (Finset.range n).sum (fun i => A i n) = (Finset.range n).sum (fun j => A n j) := Finset.sum_congr rfl (fun i _ => h i n)
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    rw [ih, hs]
    ring


-- created on 2023-05-25
-- updated on 2026-11-26
