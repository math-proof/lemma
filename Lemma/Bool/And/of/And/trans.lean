import sympy.Basic


@[main]
private lemma main
  {a b c : α}
-- given
  (h : a = b ∧ b = c) :
-- imply
  a = b ∧ a = c := by
-- proof
  exact ⟨h.1, h.1.trans h.2⟩


-- created on 2019-05-04
