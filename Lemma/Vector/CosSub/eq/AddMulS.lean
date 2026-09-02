import Lemma.Real.CosSub.eq.AddMulS
import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Vector.GetCos.eq.CosGet
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetSin.eq.SinGet
import Lemma.Vector.GetSub.eq.SubGetS
import sympy.vector.functions
open Real Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.CosSub.eq.AddMulS |
| comm | Vector.AddCosCos_SinSin.eq.CosSub |
-/
@[main, comm]
private lemma main
-- given
  (x y : List.Vector ℝ n) :
-- imply
  (x - y).cos = x.cos * y.cos + x.sin * y.sin := by
-- proof
  ext i
  rw [GetCos.eq.CosGet.fin]
  rw [GetSub.eq.SubGetS.fin]
  rw [GetAdd.eq.AddGetS.fin]
  rw [GetMul.eq.MulGetS.fin]
  rw [GetMul.eq.MulGetS.fin]
  simp [GetCos.eq.CosGet.fin, GetSin.eq.SinGet.fin]
  simp [Cos.cos, Sin.sin]
  rw [CosSub.eq.AddMulS]


-- created on 2026-09-02
