import Lemma.Nat.Ge.of.Gt
import Lemma.Int.Gt_0.of.Lt_0.Lt_0
import Lemma.Algebra.Eq.ou.Lt.of.Le
open Algebra Nat Int


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
  obtain hx | hx' := Eq.ou.Lt.of.Le h₀
  ·
    -- Case 1: x = 0
    simp_all
  ·
    -- Case 2: x < 0
    -- Use the fact that the product of two negative numbers is positive.
    have := Gt_0.of.Lt_0.Lt_0 hx' h₁
    exact Ge.of.Gt this


-- created on 2025-03-23
-- updated on 2025-04-04
