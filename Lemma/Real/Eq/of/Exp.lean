import Lemma.Bool.EqUFnS.of.Eq
open Bool


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x.exp = y.exp) :
-- imply
  x = y :=
-- proof
  Real.exp_injective h


-- created on 2025-10-02
-- updated on 2025-10-03
