import Lemma.Tensor.Einsum.eq.MulGetData_0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetMap.eq.UFnGet
import sympy.tensor.tensor
open Tensor Vector


/-- `dot` with a 0-d left factor commutes with a pointwise map `f`. -/
@[main, comm]
private lemma left
  [Mul α] [AddCommMonoid α]
  [Mul β] [AddCancelCommMonoid β]
  {f : α → β}
-- given
  (h_mul : ∀ a b, f (a * b) = f a * f b)
  (A : Tensor α [])
  (B : Tensor α s') :
-- imply
  (A @ B).map f = (A.map f) @ (B.map f) := by
-- proof
  simp only [Dot.dot]
  rw [Einsum.eq.MulGetData_0, Einsum.eq.MulGetData_0]
  apply Eq.of.EqDataS
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  simp [Tensor.map, HMul.hMul]
  simp only [GetElem.getElem]
  repeat erw [GetMap.eq.UFnGet.fin]
  simp [HMul.hMul] at h_mul
  rw [h_mul]


/-- `dot` with a 0-d right factor commutes with a pointwise map `f`. -/
@[main, comm]
private lemma main
  [Mul α] [AddCommMonoid α]
  [Mul β] [AddCancelCommMonoid β]
  {f : α → β}
-- given
  (h_mul : ∀ a b, f (a * b) = f a * f b)
  (A : Tensor α (n :: s))
  (B : Tensor α []) :
-- imply
  (A @ B).map f = (A.map f) @ (B.map f) := by
-- proof
  simp only [Dot.dot]
  unfold einsum
  simp
  apply Eq.of.EqDataS
  simp [Tensor.map]
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  simp [HMul.hMul]
  simp only [GetElem.getElem]
  repeat erw [GetMap.eq.UFnGet.fin]
  apply h_mul


-- created on 2026-08-16
-- updated on 2026-08-17
