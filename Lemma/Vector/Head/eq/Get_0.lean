import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.Head.eq.Get_0 |
| comm | Vector.Get_0.eq.Head |
| fin | Vector.Head.eq.Get_0.fin |
| fin.comm | Vector.Get_0.eq.Head.fin |
-/
@[main, comm, fin, fin.comm]
private lemma main
  {n : ℕ}
-- given
  (v : List.Vector α n.succ) :
-- imply
  v.head = v[0] := by
-- proof
  simp [GetElem.getElem]


-- created on 2025-07-11
