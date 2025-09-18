import Lemma.Algebra.LtVal
open Algebra


@[main]
private lemma main
-- given
  (i : Fin n)
  (m : ℕ) :
-- imply
  i < n + m := by
-- proof
  have := LtVal i
  linarith


-- created on 2025-05-30
