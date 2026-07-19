import Lemma.Nat.Ge.of.Gt
import Lemma.Int.Gt_0.of.Lt_0.Lt_0
import Lemma.Nat.Le.is.Lt.ou.Eq
open Nat Int


@[main]
private lemma main
  [Semiring α]
  [PartialOrder α]
  [ExistsAddOfLE α]
  [MulPosStrictMono α]
  [AddRightStrictMono α]
  [AddRightReflectLT α]
  {x y : α}
-- given
  (h₀ : x ≤ 0)
  (h₁ : y < 0) :
-- imply
  x * y ≥ 0 := by
-- proof
  obtain hx | hx := Lt.ou.Eq.of.Le h₀
  ·
    have := Gt_0.of.Lt_0.Lt_0 hx h₁
    exact Ge.of.Gt this
  ·
    simp_all


-- created on 2025-03-23
-- updated on 2025-04-04
