import sympy.sets.sets
import Lemma.Algebra.Sub.ge.Zero.is.Le
import Lemma.Algebra.Sub.le.Zero.of.Le
import Lemma.Algebra.Le_0.of.Ge_0.Le_0
open Algebra


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
  have h₀ := Sub.ge.Zero.of.Le h₀
  have h₁ := Sub.le.Zero.of.Le h₁
  have := Le_0.of.Ge_0.Le_0 h₀ h₁
  assumption


-- created on 2025-03-30
