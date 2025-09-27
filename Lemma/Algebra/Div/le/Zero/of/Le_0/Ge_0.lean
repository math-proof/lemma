import Lemma.Algebra.Eq.ou.Gt.of.Ge
import Lemma.Algebra.Div.le.Zero.of.Le_0.Gt_0
open Algebra


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h₀ : x ≤ 0)
  (h₁ : y ≥ 0) :
-- imply
  x / y ≤ 0 := by
-- proof
  obtain hy | hy := Eq.ou.Gt.of.Ge h₁
  ·
    simp_all
  ·
    apply Div.le.Zero.of.Le_0.Gt_0 h₀ hy


-- created on 2025-05-05
