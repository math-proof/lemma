import Lemma.Algebra.Eq.ou.Lt.of.Le
import Lemma.Int.Ge_0.of.Lt_0.Le_0
open Algebra Int


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
  (h₁ : y ≤ 0) :
-- imply
  x * y ≥ 0 := by
-- proof
  obtain hx | hx := Eq.ou.Lt.of.Le h₀
  -- Case 1: x = 0
  simp_all
  -- Case 2: x < 0
  apply Ge_0.of.Lt_0.Le_0 hx h₁


-- created on 2025-03-23
