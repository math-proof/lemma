import sympy.Basic


@[main]
private lemma main
  {S : Set α}
  {x : α}
-- given
  (h : x ∈ S) :
-- imply
  ∃ y ∈ S, x = y :=
-- proof
  ⟨x, h, rfl⟩


-- created on 2018-05-07
