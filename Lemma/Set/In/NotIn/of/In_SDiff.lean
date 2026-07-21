import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
  {e : α}
-- given
  (h : e ∈ A \ B) :
-- imply
  e ∈ A ∧ e ∉ B := by
-- proof
  rwa [Set.mem_sdiff] at h


-- created on 2025-04-07
