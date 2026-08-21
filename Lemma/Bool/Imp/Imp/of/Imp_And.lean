import sympy.Basic


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h : p → q ∧ r) :
-- imply
  (p → q) ∧ (p → r) :=
-- proof
  ⟨fun hp => (h hp).1, fun hp => (h hp).2⟩


-- created on 2018-08-16
-- updated on 2026-08-20
