import sympy.Basic


@[main]
private lemma given
  {p q r : Prop}
-- given
  (h : p ∨ ¬r → q ∧ r) :
-- imply
  (p → q) ∧ r := by
-- proof
  by_cases hr : r
  ·
    exact ⟨fun hp => (h (Or.inl hp)).1, hr⟩
  ·
    exact absurd (h (Or.inr hr)).2 hr


-- created on 2023-04-05
