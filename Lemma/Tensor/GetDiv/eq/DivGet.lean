import Lemma.Tensor.Div.eq.Div_GetData_0
import Lemma.Tensor.DivStack.eq.Stack_Div
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Eq_Stack
open Tensor


@[main, fin]
private lemma scalar
  [Div α]
-- given
  (X : Tensor α (n :: s))
  (a : α)
  (i : Fin n) :
-- imply
  (X / a)[i] = X[i] / a := by
-- proof
  conv in (X / a)[i] =>
    rw [Eq_Stack X]
  erw [DivStack.eq.Stack_Div.scalar]
  have := EqGetStack.fn.fin fun i : Fin n => X[i] / a
  simp [GetElem.getElem] at this ⊢
  rw [this]


@[main, fin]
private lemma main
  [Div α]
-- given
  (X : Tensor α (n :: s))
  (A : Tensor α [])
  (i : Fin n) :
-- imply
  (X / A)[i] = X[i] / A := by
-- proof
  rw [Div.eq.Div_GetData_0]
  rw [scalar]
  rw [← Div.eq.Div_GetData_0]


-- created on 2025-09-24
-- updated on 2026-08-15
