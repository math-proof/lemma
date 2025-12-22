import Lemma.Rat.LtInvS.of.Gt.Gt_0
import Lemma.Int.Lt.is.Gt0Sub
open Rat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h₀ : y > 0)
  (h₁ : x > y) :
-- imply
  x⁻¹ - y⁻¹ < 0 := by
-- proof
  apply Gt0Sub.of.Lt
  apply LtInvS.of.Gt.Gt_0 h₀ h₁


-- created on 2025-03-15
