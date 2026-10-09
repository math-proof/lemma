import sympy.Basic


@[path]
private lemma main
  {x : α}
  {U S s : Set α}
-- given
  (h : x ∈ S \ s)
  (hU : S ⊆ U) :
-- imply
  x ∈ U \ s := by
-- proof
  exact ⟨hU h.1, h.2⟩


-- created on 2021-03-03
