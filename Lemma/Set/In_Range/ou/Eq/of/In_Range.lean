import sympy.sets.sets
import Lemma.Set.Lt.ou.Eq.of.In_Range
import Lemma.Set.In_Range.of.Lt
open Set


@[main]
private lemma main
  {n i : ℕ}
-- given
  (h : i ∈ Finset.range (n + 1)) :
-- imply
  i ∈ Finset.range n ∨ i = n := by
-- proof
  have := Lt.ou.Eq.of.In_Range h
  obtain h_Lt | h_Eq := this
  ·
    exact Or.inl (In_Range.of.Lt h_Lt)
  ·
    exact Or.inr h_Eq


-- created on 2025-04-26
