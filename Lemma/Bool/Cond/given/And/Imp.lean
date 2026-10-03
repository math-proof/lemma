import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : q)
  (hp : p) :
-- imply
  (p → q) ∧ p := by
-- proof
  exact ⟨fun _ => h, hp⟩


-- created on 2023-04-18
