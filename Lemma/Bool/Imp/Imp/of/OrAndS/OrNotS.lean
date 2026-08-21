import sympy.Basic


@[main]
private lemma main
  {p0 q0 p1 q1 : Prop}
-- given
  (h₀ : ¬p0 ∨ ¬p1)
  (h₁ : p0 ∧ q0 ∨ p1 ∧ q1) :
-- imply
  (p0 → q0) ∧ (p1 → q1) := by
-- proof
  constructor
  ·
    intro hp0
    have hp1f : ¬p1 := h₀.resolve_left (not_not.mpr hp0)
    exact (h₁.resolve_right (fun h => hp1f h.1)).2
  ·
    intro hp1
    have hp0f : ¬p0 := h₀.resolve_right (not_not.mpr hp1)
    exact (h₁.resolve_left (fun h => hp0f h.1)).2


-- created on 2022-04-01
-- updated on 2026-08-20
