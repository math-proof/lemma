import Lemma.Algebra.Ge.of.Gt
import Lemma.Algebra.Eq.ou.Gt.of.Ge
import Lemma.Algebra.Gt_0.of.Gt_0.Gt_0
open Algebra


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [PosMulStrictMono α]


  {x y : α}
-- given
  (h₀ : x > 0)
  (h₁ : y ≥ 0) :
-- imply
  x * y ≥ 0 := by
-- proof
  obtain hy | hy := Eq.ou.Gt.of.Ge h₁
  simp_all
  have := Gt_0.of.Gt_0.Gt_0 h₀ hy
  exact Ge.of.Gt this


-- created on 2025-03-23
