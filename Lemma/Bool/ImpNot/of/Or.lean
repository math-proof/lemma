import sympy.Basic


@[main]
private lemma main
  {a b c : Prop}
-- given
  (h : ¬a ∨ ¬b ∨ c) :
-- imply
  a ∧ b → c := by
-- proof
  intro ⟨ha, hb⟩
  obtain h | h | h := h
  · exact absurd ha h
  · exact absurd hb h
  · exact h


-- created on 2018-03-21
