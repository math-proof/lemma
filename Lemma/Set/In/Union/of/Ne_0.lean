import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ≠ 0) :
-- imply
  x ∈ Set.univ \ {0} :=
-- proof
  ⟨trivial, h⟩


-- created on 2023-05-02
