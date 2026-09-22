import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
  {f : β → α}
-- given
  (h : ∃ e, p (f e)) :
-- imply
  ∃ x, p x := by
-- proof
  let ⟨e, he⟩ := h
  exact ⟨f e, he⟩


-- created on 2019-02-16
