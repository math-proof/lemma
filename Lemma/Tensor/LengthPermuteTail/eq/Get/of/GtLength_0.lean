import Theorem.Tensor.Length.eq.Get_0.of.GtLength_0
import Notation.Data.Tensor.Permute
open Tensor


@[path]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  (X.permuteTail s.length).length = s[s.length - 1] := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  ·
    simp [List.rotate]
    grind
  ·
    simpa using h


-- created on 2026-04-08
-- updated on 2026-11-22
