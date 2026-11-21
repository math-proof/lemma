module
public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic


@[path, comm, fin, fin.comm]
private theorem main
  [Neg α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (-x)[i] = -x[i] := by
-- proof
  simp [Neg.neg]


-- created on 2025-10-04
