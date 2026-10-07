import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {U : Set ℤ} :
-- imply
  U \ {n : ℤ | n % 2 = 0} = {n ∈ U | n % 2 = 1} := by
-- proof
  ext n
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
  if hu : n ∈ U then
    simp only [hu, true_and]
    omega
  else
    simp [hu]


-- created on 2018-04-28
