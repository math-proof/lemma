import sympy.Basic


@[path]
private lemma main
  {s : Set α}
  {p : α → Prop} :
-- imply
  {x ∈ s | p x} = {x | p x} ∩ s := by
-- proof
  ext x
  exact and_comm


-- created on 2020-12-22
-- updated on 2026-10-17
