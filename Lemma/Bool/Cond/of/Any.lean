import sympy.Basic


@[main]
private lemma main
-- given
  (h : ∃ _ : α, r) :
-- imply
  r := by
-- proof
  let ⟨_, hr⟩ := h
  exact hr


-- created on 2024-07-01
