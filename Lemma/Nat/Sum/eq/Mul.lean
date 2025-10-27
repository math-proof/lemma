import Lemma.Finset.Sum.eq.MulCard
open Finset


@[main]
private lemma main
  [NonAssocSemiring α]
-- given
  (n : ℕ)
  (x : α) :
-- imply
  ∑ _ : Fin n, x = n * x := by
-- proof
  simp


-- created on 2025-07-19
