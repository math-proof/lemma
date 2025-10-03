import Lemma.Algebra.Lt_Sub.of.LtAdd
open Algebra


@[main]
private lemma main
  {v : List α}
-- given
  (h : n + j < v.length) :
-- imply
  have : j < (v.drop n).length := by simp_all [Lt_Sub.of.LtAdd.left.nat]
  (v.drop n)[j] = v[n + j] := by
-- proof
  simp_all


-- created on 2025-06-07
-- updated on 2025-06-28
