import Lemma.Real.SinSub.eq.SubMulSSin_Cos
import Lemma.Vector.GetCos.eq.CosGet
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetSin.eq.SinGet
import Lemma.Vector.GetSub.eq.SubGetS
import sympy.vector.functions
open Real Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.SinSub.eq.SubMulSSin_Cos |
| comm | Vector.SubMulSSin_Cos.eq.SinSub |
-/
@[main, comm]
private lemma main
-- given
  (x y : List.Vector ℝ n) :
-- imply
  (x - y).sin = x.sin * y.cos - y.sin * x.cos := by
-- proof
  ext i
  rw [GetSin.eq.SinGet.fin]
  rw [GetSub.eq.SubGetS.fin]
  rw [GetSub.eq.SubGetS.fin]
  rw [GetMul.eq.MulGetS.fin]
  rw [GetMul.eq.MulGetS.fin]
  simp [GetSin.eq.SinGet.fin, GetCos.eq.CosGet.fin]
  simp [Sin.sin, Cos.cos]
  rw [SinSub.eq.SubMulSSin_Cos]


-- created on 2026-09-02
