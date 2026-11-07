import Instance.Data.Vector.Functions.Part2
open Exp


@[path]
private lemma main
  [Exp α]
-- given
  (x : List.Vector α n) :
-- imply
  x.softmax = exp x / (exp x).sum := by
-- proof
  unfold List.Vector.softmax
  simp


-- created on 2025-10-03
-- updated on 2026-11-07
