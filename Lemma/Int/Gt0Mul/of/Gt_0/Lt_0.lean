import Lemma.Int.Gt0Mul.of.Lt_0.Gt_0
import Lemma.Nat.Mul
open Nat Int


@[main]
private lemma main
  [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h₀ : x > 0)
  (h₁ : y < 0) :
-- imply
  x * y < 0 := by
-- proof
  have := Gt0Mul.of.Lt_0.Gt_0 h₁ h₀
  rwa [Mul.comm] at this


-- created on 2025-07-20
