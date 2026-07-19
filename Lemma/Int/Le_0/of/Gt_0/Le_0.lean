import Lemma.Nat.Le.is.Lt.ou.Eq
import Lemma.Nat.Le.of.Lt
import Lemma.Int.Lt_0.of.Gt_0.Lt_0
open Nat Int


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [PosMulStrictMono α]
  {x y : α}
-- given
  (h₀ : x > 0)
  (h₁ : y ≤ 0) :
-- imply
  x * y ≤ 0 := by
-- proof
  obtain hy | hy := Lt.ou.Eq.of.Le h₁
  .
    apply Le.of.Lt
    apply Lt_0.of.Gt_0.Lt_0 h₀ hy
  .
    simp_all


-- created on 2025-03-24
