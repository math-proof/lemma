import Lemma.Algebra.NegSucc.eq.NegCoeAdd_1
open Algebra


@[main]
private lemma main
  {n : ℕ} :
-- imply
  Int.negSucc n = -(n + 1) :=
-- proof
  NegSucc.eq.NegCoeAdd_1


-- created on 2025-03-27
