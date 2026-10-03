import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {P : α → Prop}
  {Q : Prop}
-- given
  (hcond : Q)
  (h : ∃ x | x ∈ A, P x) :
-- imply
  ∃ x | x ∈ A, P x ∧ Q := by
-- proof
  obtain ⟨x, hx, hp⟩ := h
  exact ⟨x, hx, hp, hcond⟩


-- created on 2026-10-03
