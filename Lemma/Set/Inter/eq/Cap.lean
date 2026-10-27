import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A B : Set α} :
-- imply
  A ∩ B = ⋂ i : Fin 2, if i = 0 then A else B := by
-- proof
  ext x
  simp [Fin.forall_fin_two]


-- created on 2021-04-28
-- updated on 2026-10-26
