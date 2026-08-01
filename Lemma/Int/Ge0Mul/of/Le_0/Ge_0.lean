import Lemma.Nat.Le.is.Lt.ou.Eq
import Lemma.Int.Ge0Mul.of.Le_0.Gt_0
open Int Nat


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [MulPosStrictMono α]
  {x y : α}
-- given
  (h₀ : x ≤ 0)
  (h₁ : y ≥ 0) :
-- imply
  x * y ≤ 0 := by
-- proof
  obtain hy | hy := Eq.ou.Lt.of.Ge h₁
  ·
    aesop
  ·
    apply Ge0Mul.of.Le_0.Gt_0 h₀ hy


-- created on 2018-02-10
-- updated on 2026-07-31
