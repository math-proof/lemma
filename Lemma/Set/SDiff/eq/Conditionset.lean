import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A B : Set ℤ}
  {f : ℤ → ℤ} :
-- imply
  {x ∈ A | f x > 0} \ B = {x ∈ A \ B | f x > 0} := by
-- proof
  ext x
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
  tauto


-- created on 2020-11-17
