import Lemma.Real.Pow_Add.eq.MulPowS.of.Gt_0
open Real


@[main]
private lemma main
  {t : ℝ}
-- given
  (h : t > 0)
  (x y : ℝ) :
-- imply
  t ^ x * t ^ y = t ^ (x + y) :=
-- proof
  MulPowS.eq.Pow_Add.of.Gt_0 h x y


-- created on 2020-01-30
-- updated on 2026-08-20
