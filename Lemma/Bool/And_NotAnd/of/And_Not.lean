import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p ∧ ¬q) :
-- imply
  p ∧ ¬(p ∧ q) := by
-- proof
  constructor
  ·
    exact h.left
  ·
    by_contra h'
    let ⟨_, h_q⟩ := h'
    let ⟨_, h_q⟩ := h
    contradiction


-- created on 2025-04-14
