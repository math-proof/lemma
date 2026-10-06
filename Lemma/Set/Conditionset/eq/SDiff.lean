import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a : α} :
-- imply
  {y : α | y ≠ a} = (Set.univ : Set α) \ {a} := by
-- proof
  ext y
  simp [Set.mem_diff]


-- created on 2021-02-04
