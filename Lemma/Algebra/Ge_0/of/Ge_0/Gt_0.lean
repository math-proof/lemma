import Lemma.Nat.Ge.of.Gt
import Lemma.Algebra.Gt_0.of.Gt_0.Gt_0
import Lemma.Algebra.Eq.ou.Gt.of.Ge
open Algebra Nat


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [PosMulStrictMono α]
  {x y : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : y > 0) :
-- imply
  x * y ≥ 0 := by
-- proof
  obtain hx | hx := Eq.ou.Gt.of.Ge h₀
  simp_all
  have := Gt_0.of.Gt_0.Gt_0 hx h₁
  exact Ge.of.Gt this


-- created on 2025-03-23
