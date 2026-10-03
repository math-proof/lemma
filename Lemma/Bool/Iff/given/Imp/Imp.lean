import Lemma.Bool.Iff.of.Imp.Imp
import sympy.Basic
open Bool


@[main]
private lemma main
  {p q : Prop}
-- given
  (h₀ : p → q)
  (h₁ : q → p) :
-- imply
  p ↔ q := by
-- proof
  exact Iff.of.Imp.Imp h₀ h₁


-- created on 2026-10-03
