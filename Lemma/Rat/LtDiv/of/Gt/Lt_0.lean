import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Rat.LtDivS.of.Gt.Lt_0
import Lemma.Nat.Ne.of.Lt
open Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {n d x : α}
-- given
  (h₀ : n > x * d)
  (h₁ : d < 0) :
-- imply
  n / d < x := by
-- proof
  have := LtDivS.of.Gt.Lt_0 h₀ h₁
  have h_Ne_0 := Ne.of.Lt h₁
  rwa [EqDivMul.of.Ne_0 h_Ne_0] at this


-- created on 2025-03-30
