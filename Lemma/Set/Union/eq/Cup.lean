import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A B : Set α} :
-- imply
  A ∪ B = ⋃ i : Fin 2, if i = 0 then A else B := by
-- proof
  ext x
  simp [Fin.exists_fin_two]


-- created on 2021-07-13
-- updated on 2026-10-26
