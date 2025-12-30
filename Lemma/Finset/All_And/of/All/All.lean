import sympy.Basic
import sympy.concrete.quantifier


@[main]
private lemma main
  {f g : ι → Prop}
  {s : Finset ι}
-- given
  (h₀ : ∀ i ∈ s, f i)
  (h₁ : ∀ i ∈ s, g i) :
-- imply
  ∀ i ∈ s, f i ∧ g i := by
-- proof
  intro i hi
  apply And.intro
  exact h₀ i hi
  exact h₁ i hi


-- created on 2025-12-30
