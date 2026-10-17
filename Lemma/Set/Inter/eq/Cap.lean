import sympy.Basic


@[path]
private lemma main
  {A B : Set α} :
-- imply
  A ∩ B = ⋂ i : Fin 2, if i = 0 then A else B := by
-- proof
  ext x
  simp [Fin.forall_fin_two]


-- created on 2026-10-11
-- updated on 2026-10-17
