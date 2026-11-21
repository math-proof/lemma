module
public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic


@[path, fin]
private theorem main
  [Add α]
-- given
  (a b : List.Vector α n)
  (i : Fin n) :
-- imply
  (a + b)[i] = a[i] + b[i] := by
-- proof
  conv in a + b =>
    simp [HAdd.hAdd]
  simp [Add.add]
  simp [GetElem.getElem]


-- created on 2025-07-14
