import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α]
  {n : ℕ}
  {f g : ℕ → α} :
-- imply
  ∑ k ∈ Finset.range n, f k - ∑ k ∈ Finset.range n, g k = ∑ k ∈ Finset.range n, (f k - g k) :=
-- proof
  (Finset.sum_sub_distrib f g).symm


-- created on 2026-09-27
