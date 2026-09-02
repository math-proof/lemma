import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Map₂.eq.Map.of.Eq_1
import sympy.tensor.Basic
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Add |
| comm | Tensor.Add.comm |
-/
@[main, comm]
private lemma main
  [Add α]
-- given
  (X Y : Tensor α []) :
-- imply
  X + Y = Add.add X Y := by
-- proof
  apply Eq.of.EqDataS
  simp [HAdd.hAdd, Add.add]
  erw [Map₂.eq.Map.of.Eq_1 (n := [].prod) (by rfl)]
  rfl


-- created on 2026-09-02
