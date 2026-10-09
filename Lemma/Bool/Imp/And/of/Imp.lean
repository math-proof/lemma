import sympy.Basic


@[path]
private lemma main
  {p q : Prop}
-- given
  (h : p → q) :
-- imply
  p → p ∧ q :=
-- proof
  fun hp => ⟨hp, h hp⟩


@[path]
private lemma domain_defined
  {p q c : Prop}
-- given
  (h : p → q) :
-- imply
  c ∧ p → q :=
-- proof
  fun hcp => h hcp.2


-- created on 2023-05-03
