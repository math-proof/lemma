import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {α : Type*}
  {S : Finset α}
  {x : α}
-- given
  (h : x ∈ S) :
-- imply
  1 ≤ S.card := by
-- proof
  exact Finset.one_le_card.mpr ⟨x, h⟩


-- created on 2021-03-10
