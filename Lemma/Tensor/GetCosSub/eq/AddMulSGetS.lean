import Lemma.Tensor.CosSub.eq.AddMulS
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.GetMul.eq.MulGetS
import sympy.tensor.functions
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetCosSub.eq.AddMulSGetS |
| fin | Tensor.GetCosSub.eq.AddMulSGetS.fin |
| comm | Tensor.AddMulSGetS.eq.GetCosSub |
| fin.comm | Tensor.AddMulSGetS.eq.GetCosSub.fin |
-/
@[main, fin, comm, fin.comm]
private lemma main
-- given
  (X Y : Tensor ℝ (n :: s))
  (i : Fin n) :
-- imply
  (X - Y).cos[i] = X.cos[i] * Y.cos[i] + X.sin[i] * Y.sin[i] := by
-- proof
  rw [CosSub.eq.AddMulS]
  rw [GetAdd.eq.AddGetS]
  rw [GetMul.eq.MulGetS]
  rw [GetMul.eq.MulGetS]


-- created on 2026-09-02
