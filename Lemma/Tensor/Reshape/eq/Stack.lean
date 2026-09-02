import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetReshape.as.Reshape.of.GtLength_0
import Lemma.Tensor.SEqReshape.of.Eq
import sympy.tensor.stack
open Bool Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Reshape.eq.Stack |
| comm | Tensor.Stack.eq.Reshape |
-/
@[main, comm]
private lemma main
-- given
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  X.reshape (n :: s) (by simp) = [_ < n] X := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.SEq
  have hR := GetReshape.as.Reshape.of.GtLength_0 (s' := [n]) (by simp) X i
  have hX := SEqReshape.of.Eq (s' := s) rfl X
  have hS := EqGetStack (fun _ : Fin n => X) i
  exact (hR.trans hX).trans (SEq.of.Eq hS.symm)


-- created on 2026-09-02
