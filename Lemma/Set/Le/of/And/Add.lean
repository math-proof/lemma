import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b t : ℝ}
-- given
  (h : a ≤ b) :
-- imply
  a + t ≤ b + t ∧ t ∈ Set.univ :=
-- proof
  ⟨add_le_add_left h t, Set.mem_univ t⟩


-- created on 2021-05-19
