import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p → q) :
-- imply
  p → p ∧ q :=
-- proof
  fun hp => ⟨hp, h hp⟩


@[main]
private lemma domain_defined
  {p q c : Prop}
-- given
  (h : p → q) :
-- imply
  c ∧ p → q :=
-- proof
  fun hcp => h hcp.2


-- created on 2026-09-27
