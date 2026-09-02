import sympy.vector.functions
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.GetSin.eq.SinGet |
| fin | Vector.GetSin.eq.SinGet.fin |
| comm | Vector.SinGet.eq.GetSin |
| fin.comm | Vector.SinGet.eq.GetSin.fin |
-/
@[main, fin, comm, fin.comm]
private lemma main
  [Sin α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  x.sin[i] = Sin.sin x[i] := by
-- proof
  simp [List.Vector.sin]


-- created on 2026-09-02
