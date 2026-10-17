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


-- created on 2026-10-11
-- updated on 2026-10-17
