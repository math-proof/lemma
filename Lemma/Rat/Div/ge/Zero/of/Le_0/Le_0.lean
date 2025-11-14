import Lemma.Rat.EqDiv0'0
import Lemma.Rat.LeDivS.of.Ge.Le_0
open Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h₀ : a ≤ 0)
  (h₁ : b ≤ 0) :
-- imply
  a / b ≥ 0 := by
-- proof
  have h := LeDivS.of.Ge.Le_0 h₀ h₁
  simp only [EqDiv0'0] at h
  exact h


-- created on 2025-03-30
