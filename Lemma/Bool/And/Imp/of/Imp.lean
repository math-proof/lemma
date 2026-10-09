import sympy.Basic


@[path]
private lemma split
-- given
  (h : p → q) :
-- imply
  (p ∧ c → q) ∧ (p ∧ ¬c → q) :=
-- proof
  ⟨fun hp => h hp.1, fun hp => h hp.1⟩


-- created on 2023-04-25
