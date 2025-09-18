import sympy.concrete.quantifier
import Lemma.Basic


@[main]
private lemma main
  {p q r : α → Prop}
-- given
  (h₀ : ∀ x | r x, p x)
  (h₁ : ∃ x | r x, q x) :
-- imply
  ∃ x | r x, p x ∧ q x := by
-- proof
  let ⟨x, h_q', h_p'⟩ := h₁
  have h₀ := h₀ x
  use x
  simp_all


@[main]
private lemma set
  {A : Set α}
  {f : α → Prop}
  {g : α → Prop}
-- given
  (h₀ : ∀ x ∈ A, g x)
  (h₁ : ∃ x ∈ A, f x) :
-- imply
  ∃ x ∈ A, g x ∧ f x := by
-- proof
  apply main h₀ h₁

-- created on 2025-05-01
