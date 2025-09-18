import Lemma.Algebra.Eq.ou.Gt.of.Ge
import Lemma.Algebra.Le.of.Lt
import Lemma.Algebra.Mul.lt.Zero.of.Lt_0.Gt_0
open Algebra


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [MulPosStrictMono α]
  {x y : α}
-- given
  (h₀ : x < 0)
  (h₁ : y ≥ 0) :
-- imply
  x * y ≤ 0 := by
-- proof
  obtain hy | hy := Eq.ou.Gt.of.Ge h₁
  simp_all
  apply Le.of.Lt
  apply Mul.lt.Zero.of.Lt_0.Gt_0 h₀ hy


-- created on 2025-03-23
-- updated on 2025-03-24
