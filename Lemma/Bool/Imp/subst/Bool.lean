import sympy.Basic


@[main]
private lemma main
  {c p : Prop} [Decidable c]
  {u v : α}
  {P : α → Prop} :
-- imply
  (c ∧ p → P (if c then u else v)) ↔ (c ∧ p → P u) := by
-- proof
  constructor
  ·
    intro h hcp
    have h' := h hcp
    rwa [if_pos hcp.1] at h'
  ·
    intro h hcp
    rw [if_pos hcp.1]
    exact h hcp


-- created on 2026-09-27
