import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main:
-- imply
  p ∧ q ∨ r ↔ (p ∨ r) ∧ (q ∨ r) := by
-- proof
  constructor <;>
    intro h
  .
    cases h with
    | inl hpq =>
      have hp : p := hpq.left
      have hq : q := hpq.right
      exact ⟨Or.inl hp, Or.inl hq⟩
    | inr hr =>
      exact ⟨Or.inr hr, Or.inr hr⟩
  .
    have hpr : p ∨ r := h.left
    have hqr : q ∨ r := h.right
    cases hpr with
    | inl hp =>
      cases hqr with
      | inl hq =>
        exact Or.inl ⟨hp, hq⟩
      | inr hr =>
        exact Or.inr hr
    | inr hr =>
      exact Or.inr hr


-- created on 2024-07-01
