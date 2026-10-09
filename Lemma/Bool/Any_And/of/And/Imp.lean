import sympy.Basic


@[path]
private lemma main
  {q r : α → Prop}
-- given
  (h : (p → ∃ x, q x) ∧ (¬p → ∃ x, r x)) :
-- imply
  ∃ x, (p → q x) ∧ (¬p → r x) := by
-- proof
  by_cases hp : p
  ·
    obtain ⟨x, hx⟩ := h.1 hp
    exact ⟨x, fun _ => hx, fun hn => absurd hp hn⟩
  ·
    obtain ⟨x, hx⟩ := h.2 hp
    exact ⟨x, fun h' => absurd h' hp, fun _ => hx⟩


-- created on 2023-07-01
