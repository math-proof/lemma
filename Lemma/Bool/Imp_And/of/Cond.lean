import sympy.Basic


@[main]
private lemma main
-- given
  (h : q) :
-- imply
  p → p ∧ q :=
-- proof
  fun hp => ⟨hp, h⟩


-- created on 2018-08-30
