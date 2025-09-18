import Lemma.Algebra.LengthMap.eq.Length
open Algebra


@[main]
private lemma main
-- given
  (s : List ℕ) :
-- imply
  (s.map List.range).map List.length = s := by
-- proof
  ext i k
  simp_all


-- created on 2025-06-11
