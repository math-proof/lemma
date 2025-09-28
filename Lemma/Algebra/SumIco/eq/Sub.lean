import Lemma.Algebra.Sum.eq.MulCard
open Algebra


@[main]
private lemma main
-- given
  (b a : ℕ) :
-- imply
  ∑ _ ∈ Finset.Ico a b, 1 = b - a := by
-- proof
  simp


-- created on 2025-04-06
-- updated on 2025-07-19
