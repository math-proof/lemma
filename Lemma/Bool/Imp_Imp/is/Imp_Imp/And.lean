import sympy.Basic


@[main]
private lemma main
  {p q r : Prop} :
-- imply
  (r → p → q) ↔ (r → p → q ∧ r) := by
-- proof
  constructor
  ·
    intro h hr hp
    exact ⟨h hr hp, hr⟩
  ·
    intro h hr hp
    exact (h hr hp).1


-- created on 2019-10-09
