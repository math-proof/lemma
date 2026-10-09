import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h : x ∈ Set.Ioo a b) :
-- imply
  x ∈ Set.Ico a b :=
-- proof
  ⟨le_of_lt h.1, h.2⟩


-- created on 2021-02-27
