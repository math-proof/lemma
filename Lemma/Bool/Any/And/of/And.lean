import sympy.Basic


@[main]
private lemma main
  {B : Set β}
  {p : Prop}
  {q : β → Prop}
-- given
  (h : p ∧ ∃ b ∈ B, q b) :
-- imply
  ∃ b ∈ B, p ∧ q b := by
-- proof
  obtain ⟨hp, b, hb, hq⟩ := h
  exact ⟨b, hb, hp, hq⟩


-- created on 2019-05-07
