import sympy.Basic


@[path]
private lemma main
  {x : α}
  {S : Set α}
-- given
  (h : x ∉ S) :
-- imply
  x ∈ Set.univ \ S :=
-- proof
  ⟨Set.mem_univ x, h⟩


-- created on 2023-05-21
