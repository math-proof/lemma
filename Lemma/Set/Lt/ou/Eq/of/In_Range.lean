import sympy.sets.sets
import Lemma.Nat.Le.is.Lt.ou.Eq
import Lemma.Nat.Le.of.Lt_Add_1
import Lemma.Set.Lt.of.In_Range
open Set Nat


@[main]
private lemma main
  {n i : ℕ}
-- given
  (h : i ∈ Finset.range (n + 1)) :
-- imply
  i < n ∨ i = n := by
-- proof
  apply Lt.ou.Eq.of.Le
  apply Le.of.Lt_Add_1
  apply Lt.of.In_Range h


-- created on 2025-04-26
