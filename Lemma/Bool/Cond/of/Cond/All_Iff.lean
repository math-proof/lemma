import Lemma.Bool.Eq.is.All_Iff
import sympy.concrete.quantifier
open Bool


@[main]
private lemma main
  {p q r : α → Prop}
-- given
  (h₀ : ∀ x, p x ↔ q x)
  (h₁ : ∀ x | p x, r x) :
-- imply
  ∀ x | q x, r x :=
-- proof
  Eq.of.All_Iff h₀ ▸ h₁


-- created on 2018-03-23
-- updated on 2026-08-28
