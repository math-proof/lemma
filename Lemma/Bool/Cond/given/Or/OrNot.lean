import Lemma.Bool.Cond.of.Or.OrNot
import sympy.Basic
open Bool


@[main]
private lemma main
  {p q : Prop}
-- given
  (h₀ : q ∨ p)
  (h₁ : ¬q ∨ p) :
-- imply
  p := by
-- proof
  exact Cond.of.Or.OrNot h₀ h₁


-- created on 2026-10-03
