import Lemma.Nat.Ge.of.Gt
import Lemma.Nat.Le.is.Lt.ou.Eq
import Lemma.Nat.Lt0Mul.of.Gt_0.Gt_0
open Nat


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
  obtain hy | hy := Eq.ou.Lt.of.Ge h₁
  .
    aesop
  .
    have := Lt0Mul.of.Gt_0.Gt_0 h₀ hy
    exact Ge.of.Gt this


-- created on 2018-07-01
