import Lemma.Rat.Sum.Square.eq.Div.Sum.Square


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (hn : n > 0) :
-- imply
  ∑ i : Fin n, (x i - (∑ j : Fin n, x j) / n) ^ 2 = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, (x i - x j) ^ 2) / n := by
-- proof
  rw [Fin.sum_univ_eq_sum_range (fun j => x j) n, Fin.sum_univ_eq_sum_range (fun i => (x i - (∑ j ∈ Finset.range n, x j) / n) ^ 2) n]
  exact Rat.Sum.Square.eq.Div.Sum.Square hn


-- created on 2026-09-27
