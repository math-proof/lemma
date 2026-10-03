import sympy.Basic


@[main]
private lemma main
  {p q c : Prop}
-- given
  (h : p → q) :
-- imply
  (p ∧ c → q) ∧ (p ∧ ¬c → q) := by
-- proof
  exact ⟨fun hpc => h hpc.1, fun hpc => h hpc.1⟩


-- created on 2023-04-25
