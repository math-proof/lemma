import Theorem.Logic.SEq
import Instance.Data.Vector.Vector


@[path]
private lemma main
  [One α]
-- given
  (h : n = n') :
-- imply
  (1 : List.Vector α n) ≃ (1 : List.Vector α n') := by
-- proof
  aesop


-- created on 2025-11-05
