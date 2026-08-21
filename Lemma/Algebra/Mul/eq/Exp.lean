import Lemma.Real.ExpAdd.eq.MulExpS
open Real


@[main]
private lemma main
  [Exp R]
  {a b : R} :
-- imply
  exp a * exp b = exp (a + b) :=
-- proof
  (ExpAdd.eq.MulExpS (a := a) (b := b)).symm


-- created on 2018-10-25
-- updated on 2026-08-20
