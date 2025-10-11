import sympy.tensor.functions
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Bool.EqUFnS.of.Eq
open Tensor Bool


@[main]
private lemma main
  [ExpPos α]
-- given
  (X : Tensor α [n]) :
-- imply
  X.softmax = ⟨X.data.softmax⟩ := by
-- proof
  let ⟨X⟩ := X
  unfold Tensor.softmax
  unfold List.Vector.softmax
  apply Eq.of.EqDataS
  rw [DataDiv.eq.DivDataS]
  simp [DataExp.eq.ExpData]
  sorry


-- created on 2025-10-11
