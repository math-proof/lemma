import Lemma.List.Eq_Nil.is.EqLength_0
import Lemma.Nat.Eq_0
import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataMul.eq.Mul_Data
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetMul.eq.Mul_Get
import sympy.tensor.tensor
open List Nat Tensor Vector


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α s)
  (Y : Tensor α []) :
-- imply
  X.matmul Y = cast (by simp [Tensor.matmul_shape]; grind) (X * Y.data[0]) := by
-- proof
  unfold Tensor.matmul
  split_ifs with h_s? h_s h_nil
  ·
    subst h_s
    simp_all
    apply Eq.of.EqDataS
    rw [DataMul.eq.MulData]
    rw [DataMul.eq.Mul_Data]
    apply Eq.of.All_EqGetS
    intro i
    have h_i := Eq_0.prod i
    subst h_i
    rw [GetMul.eq.MulGet]
    rw [GetMul.eq.Mul_Get]
    simp
    rfl
  ·
    simp
    have := Eq_Nil.of.EqLength_0 h_s?
    contradiction
  ·
    simp
  ·
    simp
  repeat simp; grind


-- created on 2026-01-06
