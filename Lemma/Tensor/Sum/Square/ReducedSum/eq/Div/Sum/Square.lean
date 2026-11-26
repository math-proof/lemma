import Lemma.Rat.Sum.Square.eq.Div.Sum.Square
import Notation.Algebra.Power
open Rat


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (hn : n > 0) :
-- imply
  ∑ i : Fin n, (x i - (∑ j : Fin n, x j) / n)² = (∑ i < n, ∑ j < i, (x i - x j)²) / n := by
-- proof
  rw [Fin.sum_univ_eq_sum_range (fun j => x j) n,
    Fin.sum_univ_eq_sum_range (fun i => (x i - (Finset.range n).sum (fun j => x j) / n)²) n]
  simpa only [Nat.Iio_eq_range] using Sum.Square.eq.Div.Sum.Square hn


-- created on 2023-10-08
-- updated on 2026-11-26
