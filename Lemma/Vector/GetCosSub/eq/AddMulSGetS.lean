import Lemma.Vector.CosSub.eq.AddMulS
import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Vector.GetMul.eq.MulGetS
import sympy.vector.functions
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.GetCosSub.eq.AddMulSGetS |
| fin | Vector.GetCosSub.eq.AddMulSGetS.fin |
| comm | Vector.AddMulSGetS.eq.GetCosSub |
| fin.comm | Vector.AddMulSGetS.eq.GetCosSub.fin |
-/
@[main, fin, comm, fin.comm]
private lemma main
-- given
  (x y : List.Vector ℝ n)
  (i : Fin n) :
-- imply
  (x - y).cos[i] = x.cos[i] * y.cos[i] + x.sin[i] * y.sin[i] := by
-- proof
  rw [CosSub.eq.AddMulS]
  rw [GetAdd.eq.AddGetS]
  rw [GetMul.eq.MulGetS]
  rw [GetMul.eq.MulGetS]


-- created on 2026-09-02
