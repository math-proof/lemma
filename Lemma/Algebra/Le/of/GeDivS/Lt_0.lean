import Lemma.Algebra.EqMulDiv.of.Ne_0
import Lemma.Algebra.LeMulS.of.Ge.Lt_0
import Lemma.Algebra.Ne.of.Lt
open Algebra


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b : α}
-- given
  (h₀ : a / x ≥ b / x)
  (h₁ : x < 0) :
-- imply
  a ≤ b := by
-- proof
  have := LeMulS.of.Ge.Lt_0 h₀ h₁
  have h₁ := Ne.of.Lt h₁
  repeat rw [EqMulDiv.of.Ne_0 h₁] at this
  assumption


-- created on 2025-03-30
