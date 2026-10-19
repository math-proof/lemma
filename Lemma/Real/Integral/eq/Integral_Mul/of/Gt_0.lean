import Lemma.Real.Integral_Mul.eq.Integral.of.Gt_0
open Real


@[path]
private lemma main
  {a b c t : ℝ}
  {f : ℝ → ℝ}
-- given
  (ht : 0 < t) :
-- imply
  ∫ x in (c + t * a)..(c + t * b), f x = ∫ x in a..b, f (c + t * x) * t := by
-- proof
  apply Eq.symm
  apply Integral_Mul.eq.Integral.of.Gt_0 ht


-- created on 2023-04-18
-- updated on 2026-10-12
