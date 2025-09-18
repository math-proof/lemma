import Lemma.Algebra.Gt_0.of.Lt_0.Lt_0
import Lemma.Algebra.Ge.of.Gt
import Lemma.Algebra.Eq.ou.Lt.of.Le
open Algebra


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
  (h₁ : y ≤ 0) :
-- imply
  x * y ≥ 0 := by
-- proof
  obtain hx | hx := Eq.ou.Lt.of.Le h₁
  simp_all
  have := Gt_0.of.Lt_0.Lt_0 h₀ hx
  exact Ge.of.Gt this


-- created on 2025-03-23
