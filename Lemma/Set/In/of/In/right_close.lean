import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h : x ∈ Set.Ioo a b) :
-- imply
  x ∈ Set.Ioc a b :=
-- proof
  ⟨h.1, le_of_lt h.2⟩


-- created on 2021-02-28
