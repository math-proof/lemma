import Lemma.Tensor.DataDiv.eq.DivData
import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataMul.eq.Mul_Data
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Mul.eq.Mul_GetData_0
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.EqDivMul.of.Ne_0
import Lemma.Vector.EqGet0_0
open Tensor Vector


private lemma NeGetData_0.of.Ne_0
  [Zero α]
  {A : Tensor α []}
  (h : A ≠ 0) :
  A.data[0] ≠ 0 := by
  intro h0
  apply h
  apply Eq.of.EqDataS
  apply Eq.of.All_EqGetS.fin
  intro i
  have hi : i.val = 0 := by
    have := i.isLt
    simp only [List.prod_nil] at this
    exact Nat.lt_one_iff.mp this
  have hi' : i = ⟨0, by simp [List.prod_nil]⟩ := Fin.eq_of_val_eq hi
  subst hi'
  rw [EqData0'0]
  rw [EqGet0_0.fin]
  exact h0


@[main]
private lemma left
  [CommMonoidWithZero α]
  [Div α]
  [MulDivCancelClass α]
  {A : Tensor α []}
-- given
  (h : A ≠ 0)
  (B : Tensor α s) :
-- imply
  A.data[0] * B / A = B := by
-- proof
  have ha := NeGetData_0.of.Ne_0 h
  apply Eq.of.EqDataS
  rw [DataDiv.eq.DivData]
  rw [DataMul.eq.Mul_Data]
  rw [Vector.EqDivMul.of.Ne_0.left ha]


@[main]
private lemma main
  [MonoidWithZero α]
  [Div α]
  [MulDivCancelClass α]
  {A : Tensor α []}
-- given
  (h : A ≠ 0)
  (B : Tensor α s) :
-- imply
  B * A / A = B := by
-- proof
  have ha := NeGetData_0.of.Ne_0 h
  rw [Mul.eq.Mul_GetData_0]
  apply Eq.of.EqDataS
  rw [DataDiv.eq.DivData]
  rw [DataMul.eq.MulData]
  rw [Vector.EqDivMul.of.Ne_0 ha]


-- created on 2026-08-16
