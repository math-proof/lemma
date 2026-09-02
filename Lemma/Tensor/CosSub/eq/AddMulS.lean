import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataCos.eq.CosData
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataSin.eq.SinData
import Lemma.Tensor.DataSub.eq.SubDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.CosSub.eq.AddMulS
import sympy.tensor.functions
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.CosSub.eq.AddMulS |
| comm | Tensor.AddCosCos_SinSin.eq.CosSub |
-/
@[main, comm]
private lemma main
-- given
  (X Y : Tensor ℝ s) :
-- imply
  (X - Y).cos = X.cos * Y.cos + X.sin * Y.sin := by
-- proof
  apply Eq.of.EqDataS
  simp [DataCos.eq.CosData]
  simp [DataSub.eq.SubDataS]
  simp [DataAdd.eq.AddDataS]
  simp [DataMul.eq.MulDataS]
  simp [CosSub.eq.AddMulS]
  simp [DataCos.eq.CosData, DataSin.eq.SinData]


-- created on 2026-09-02
