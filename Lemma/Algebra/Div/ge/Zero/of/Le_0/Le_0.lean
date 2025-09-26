import Lemma.Algebra.EqDiv0'0
import Lemma.Algebra.GeDivS.of.Le.Le_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]

  {a b : α}
-- given
  (h₀ : a ≤ 0)
  (h₁ : b ≤ 0) :
-- imply
  a / b ≥ 0 := by
-- proof
  have h := GeDivS.of.Le.Le_0 h₀ h₁
  simp only [EqDiv0'0] at h
  exact h


-- created on 2025-03-30
