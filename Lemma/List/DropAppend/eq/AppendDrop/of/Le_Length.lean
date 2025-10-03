import Lemma.Algebra.Sub.eq.Zero.of.Le
import Lemma.List.DropAppend.eq.AppendDropS
open Algebra List


@[main]
private lemma main
-- given
  (h : i ≤ a.length)
  (b : List α) :
-- imply
  (a ++ b).drop i = a.drop i ++ b := by
-- proof
  rw [DropAppend.eq.AppendDropS]
  rw [Sub.eq.Zero.of.Le h]
  simp


-- created on 2025-06-20
-- updated on 2025-10-03
