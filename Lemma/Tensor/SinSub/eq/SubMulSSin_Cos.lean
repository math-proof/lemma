import Lemma.Tensor.DataCos.eq.CosData
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataSin.eq.SinData
import Lemma.Tensor.DataSub.eq.SubDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.SinSub.eq.SubMulSSin_Cos
import sympy.tensor.functions
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.SinSub.eq.SubMulSSin_Cos |
| comm | Tensor.SubMulSSin_Cos.eq.SinSub |
-/
@[main, comm]
private lemma main
-- given
  (X Y : Tensor ℝ s) :
-- imply
  (X - Y).sin = X.sin * Y.cos - Y.sin * X.cos := by
-- proof
  apply Eq.of.EqDataS
  simp [DataSin.eq.SinData]
  simp [DataSub.eq.SubDataS]
  simp [DataMul.eq.MulDataS]
  simp [SinSub.eq.SubMulSSin_Cos]
  simp [DataSin.eq.SinData, DataCos.eq.CosData]


-- created on 2026-09-02
