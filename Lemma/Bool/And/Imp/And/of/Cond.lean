import sympy.Basic


@[path]
private lemma split
  {p c : Prop}
-- given
  (h : p) :
-- imply
  (c → p ∧ c) ∧ (¬c → p ∧ ¬c) :=
-- proof
  ⟨fun hc => ⟨h, hc⟩, fun hc => ⟨h, hc⟩⟩


-- created on 2019-03-18
