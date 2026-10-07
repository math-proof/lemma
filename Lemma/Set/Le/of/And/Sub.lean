import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b t : ℝ}
-- given
  (h : a ≤ b) :
-- imply
  a - t ≤ b - t ∧ t ∈ Set.univ :=
-- proof
  ⟨sub_le_sub_right h t, Set.mem_univ t⟩


-- created on 2021-05-19
