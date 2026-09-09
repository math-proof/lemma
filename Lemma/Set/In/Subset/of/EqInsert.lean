import sympy.Basic


@[main]
private lemma main
  {a : α}
  {s S : Set α}
-- given
  (h : insert a s = S) :
-- imply
  a ∈ S ∧ s ⊆ S := by
-- proof
  subst h
  exact ⟨Set.mem_insert a s, Set.subset_insert a s⟩


-- created on 2020-08-28
-- updated on 2026-09-09
