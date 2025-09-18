import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main :
-- imply
  p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r := by
-- proof
  constructor <;>
    intro h
  .
    cases h with
    | intro hp hqr =>
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩
  .
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => exact ⟨hp, Or.inl hq⟩
    | inr hpr =>
      cases hpr with
      | intro hp hr => exact ⟨hp, Or.inr hr⟩


@[main, comm, mp, mpr]
private lemma apart :
-- imply
  p ∧ (q ∨ r) ↔ p ∧ q ∨ r ∧ p  := by
-- proof
  rw [And.comm (b := p)]
  apply main


-- created on 2024-07-01
