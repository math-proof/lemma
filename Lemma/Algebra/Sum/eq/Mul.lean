import Lemma.Algebra.Sum.eq.MulCard
open Algebra


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
