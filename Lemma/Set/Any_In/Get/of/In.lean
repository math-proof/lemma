import sympy.Basic


@[main]
private lemma main
  {ι α : Type*}
  {x : ι → α}
  {S : Set (ι → α)}
  {i : ι}
-- given
  (h : x ∈ S) :
-- imply
  ∃ a ∈ S, x i = a i := by
-- proof
  exact ⟨x, h, rfl⟩


-- created on 2021-03-02
