import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
  [Mul α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x * a)[i] = x[i] * a := by
-- proof
  simp [HMul.hMul]


@[main]
private lemma fin
  [Mul α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x * a).get i = x.get i * a := by
-- proof
  apply main


-- created on 2025-09-22
