import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
  {e : α}
-- given
  (h : e ∉ A ∩ B) :
-- imply
  e ∉ A ∨ e ∉ B := by
-- proof
  if ha : e ∈ A then
    apply Or.inr
    intro hb
    apply h
    exact Set.mem_inter ha hb
  else
    apply Or.inl ha


-- created on 2021-08-21
