import sympy.Basic


@[main]
private lemma main
  [DecidableEq ι]
  {A B : Finset ι}
  {x : ι}
-- given
  (h : x ∉ A ∪ B) :
-- imply
  x ∉ A ∧ x ∉ B := by
-- proof
  constructor <;> 
    simp_all [Finset.mem_union]


-- created on 2025-12-30
