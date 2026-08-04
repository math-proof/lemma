import sympy.sets.sets
import Lemma.Int.Le0Sub.is.Ge
import Lemma.Int.Ge0Sub.is.Le
import Lemma.Int.Le_0.of.Ge_0.Le_0
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  (x - a) * (x - b) ≤ 0 := by
-- proof
  let ⟨h₀, h₁⟩ := h
  have h₀ := Le0Sub.of.Ge h₀
  have h₁ := Ge0Sub.of.Le h₁
  have := Le_0.of.Ge_0.Le_0 h₀ h₁
  assumption


-- created on 2025-03-30
