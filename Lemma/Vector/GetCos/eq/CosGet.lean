import sympy.vector.functions
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetCos.eq.CosGet |
| fin | Vector.GetCos.eq.CosGet.fin |
| comm | Vector.CosGet.eq.GetCos |
| fin.comm | Vector.CosGet.eq.GetCos.fin |
-/
@[path, fin, comm, fin.comm]
private lemma main
  [Cos α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  x.cos[i] = Cos.cos x[i] := by
-- proof
  simp [List.Vector.cos]


-- created on 2026-09-02
