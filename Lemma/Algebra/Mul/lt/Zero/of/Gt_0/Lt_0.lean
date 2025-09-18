import Lemma.Algebra.Mul.lt.Zero.of.Lt_0.Gt_0
import Lemma.Algebra.Mul
open Algebra


@[main]
private lemma int
  {x y : ℤ}
-- given
  (h₀ : x > 0)
  (h₁ : y < 0) :
-- imply
  x * y < 0 := by
-- proof
  have := Mul.lt.Zero.of.Lt_0.Gt_0.int h₁ h₀
  rw [Mul.comm] at this
  assumption


@[main]
private lemma main
  [LinearOrderedField α]
  -- [LinearOrderedRing α] does not work
  {x y : α}
-- given
  (h₀ : x > 0)
  (h₁ : y < 0) :
-- imply
  x * y < 0 := by
-- proof
  have := Mul.lt.Zero.of.Lt_0.Gt_0 h₁ h₀
  rw [Mul.comm] at this
  assumption


-- created on 2025-07-20
