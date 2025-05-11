import stdlib.List.Vector
import Lemma.Algebra.EqLengthS.of.EqFlattenSMap.Gt_0
import Lemma.Algebra.Eq.of.EqFlattenSMap.EqLengthS
open Algebra


@[main]
private lemma main
  {a b : List (List.Vector α n)}
-- given
  (h₀ : n > 0)
  (h₁ : (a.map List.Vector.toList).flatten = (b.map List.Vector.toList).flatten) :
-- imply
  a = b := by
-- proof
  have h_Eq := EqLengthS.of.EqFlattenSMap.Gt_0 h₀ h₁
  apply Eq.of.EqFlattenSMap.EqLengthS h_Eq h₁


-- created on 2025-05-11
