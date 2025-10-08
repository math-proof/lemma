import Lemma.Algebra.Ge_0.of.Lt_0.Le_0
import Lemma.Nat.Ge.of.Gt
open Algebra Nat


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
  (h₀ : x < 0)
  (h₁ : y < 0) :
-- imply
  x * y ≥ 0 := by
-- proof
  apply Ge_0.of.Lt_0.Le_0 h₀
  apply Ge.of.Gt h₁


-- created on 2025-03-23
