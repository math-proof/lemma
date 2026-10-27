import Theorem.Data.Vector.Basic.Part2


@[path, comm, fin, fin.comm]
private lemma main
  [Neg α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (-x)[i] = -x[i] := by
-- proof
  simp [Neg.neg]


-- created on 2025-10-04
