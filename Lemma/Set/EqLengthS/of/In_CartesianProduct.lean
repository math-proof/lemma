import stdlib.List
import Lemma.Set.EqLengthS.of.In_Product
import Lemma.Algebra.LengthMap.eq.Length
open Set Algebra


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : v ∈ s.cartesianProduct) :
-- imply
  v.length = s.length := by
-- proof
  unfold List.cartesianProduct at h
  have h := EqLengthS.of.In_Product h
  rwa [LengthMap.eq.Length] at h


-- created on 2025-06-29
