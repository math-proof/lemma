import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.Eq.is.EqDataS
import Theorem.Vector.GetAdd.eq.AddGetS
import Theorem.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.Eq.is.All_EqGetS
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.DivAdd.eq.AddDivS |
| comm | Tensor.AddDivS.eq.DivAdd |
-/
@[path, comm]
private lemma main
  [DivisionSemiring α]
-- given
  (A B C : Tensor α s) :
-- imply
  (A + B) / C = A / C + B / C := by
-- proof
  apply Eq.of.EqDataS
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  rw [DataDiv.eq.DivDataS, DataAdd.eq.AddDataS, GetDiv.eq.DivGetS.fin, GetAdd.eq.AddGetS.fin]
  rw [DataAdd.eq.AddDataS, GetAdd.eq.AddGetS.fin]
  rw [DataDiv.eq.DivDataS, DataDiv.eq.DivDataS]
  rw [GetDiv.eq.DivGetS.fin, GetDiv.eq.DivGetS.fin]
  apply add_div


-- created on 2026-08-15
-- updated on 2026-11-20
