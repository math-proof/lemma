import Lemma.Algebra.Eq.ou.Lt.of.Le
import Lemma.Nat.Le.of.Lt
import Lemma.Algebra.Mul.lt.Zero.of.Lt_0.Gt_0
open Algebra Nat


@[main]
private lemma main
  [MulZeroClass α]
  [PartialOrder α]
  [MulPosStrictMono α]
  {x y : α}
-- given
  (h₀ : x ≤ 0)
  (h₁ : y > 0) :
-- imply
  x * y ≤ 0 := by
-- proof
  obtain hx | hx := Eq.ou.Lt.of.Le h₀
  ·
    simp_all
  ·
    apply Le.of.Lt
    apply Mul.lt.Zero.of.Lt_0.Gt_0 hx h₁


-- created on 2025-03-23
-- updated on 2025-05-05
