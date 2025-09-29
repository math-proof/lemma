import sympy.Basic


@[main]
private lemma main
  {ι : Sort u_1}
  {f : ι → α}
  {x : α} :
-- imply
  x ∈ Set.range f ↔ ∃ (y : ι), f y = x :=
-- proof
  Set.mem_range


-- created on 2025-04-04
