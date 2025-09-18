import sympy.concrete.quantifier
import Lemma.Logic.Any_And.of.Any.All.All_Imp
open Logic


@[main]
private lemma main
  {p q : α → Prop}
  {A S : Set α}
-- given
  (h₀ : A ⊆ S)
  (h₁ : ∀ x ∈ S, p x)
  (h₂ : ∃ x ∈ A, q x) :
-- imply
  ∃ x ∈ A, p x ∧ q x :=
-- proof
  Any_And.of.Any.All.All_Imp h₀ h₁ h₂


-- created on 2025-04-28
