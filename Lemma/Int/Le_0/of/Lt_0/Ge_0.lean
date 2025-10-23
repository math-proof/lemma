import Lemma.Nat.Eq.ou.Gt.of.Ge
import Lemma.Nat.Le.of.Lt
import Lemma.Int.Mul.lt.Zero.of.Lt_0.Gt_0
open Nat Int


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
