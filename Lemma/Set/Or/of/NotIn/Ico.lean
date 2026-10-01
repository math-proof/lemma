import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {e a b : α}
-- given
  (h : e ∉ Set.Ico a b) :
-- imply
  e < a ∨ e ≥ b := by
-- proof
  by_contra hne
  push Not at hne
  exact h ⟨hne.1, hne.2⟩


-- created on 2026-09-27
