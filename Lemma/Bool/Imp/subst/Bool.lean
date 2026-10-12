import sympy.Basic


@[path]
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
    rwa [ite_eq_left hcp.1] at h'
  ·
    intro h hcp
    rw [ite_eq_left hcp.1]
    exact h hcp


-- created on 2019-10-06
-- updated on 2026-10-12
