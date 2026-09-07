import sympy.tensor.Basic
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Vector.GetNeg.eq.NegGet
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.ItemNeg.eq.NegItem |
| comm | Tensor.NegItem.eq.ItemNeg |
-/
@[main, comm]
private lemma main
  [Neg α]
-- given
  (a : Tensor α []) :
-- imply
  (-a).item = -a.item := by
-- proof
  unfold Tensor.item
  rw [DataNeg.eq.NegData]
  exact GetNeg.eq.NegGet.fin a.data ⟨0, Nat.zero_lt_one⟩


-- created on 2026-09-07
