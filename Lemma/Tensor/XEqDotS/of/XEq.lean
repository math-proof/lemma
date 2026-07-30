import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Dot
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetDot.eq.Dot_GetT
import Lemma.Tensor.XEq.is.All_XEqGetS.of.GtLength_0
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Tensor.XEqSumS.of.XEq.Ge_0
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.XEq.is.All_XEqGetS
import Lemma.Hyperreal.XEqMulS.of.XEq.Imp_XEqInvS
import sympy.tensor.tensor
open Tensor Hyperreal Vector
set_option maxHeartbeats 1000000


def tensor_col (X : Tensor ℝ* [n, m]) (j : Fin m) : Tensor ℝ* [n] :=
  Xᵀ[j]


def tensor_row (X : Tensor ℝ* [m, n]) (i : Fin m) : Tensor ℝ* [n] :=
  X[i]


/-- `All_Imp_XEqInvS` / vector dot: `A @ c ≈ B @ c` from matching `h_xinfty`, `h_pos`, and `h`. -/
private lemma dot_vec
  {A B c : Tensor ℝ* [n]}
  (h_xinfty : ∀ i : Fin n, (c.data[i] → ∞) → A.data[i]⁻¹ ≈ B.data[i]⁻¹)
  (h_pos : B * c ≥ 0)
  (h : A ≈ B) :
  A @ c ≈ B @ c := by
  rw [Dot.eq.SumMul__0, Dot.eq.SumMul__0]
  have h_mul : A * c ≈ B * c := by
    apply XEq.of.XEqDataS
    rw [DataMul.eq.MulDataS, DataMul.eq.MulDataS]
    refine Vector.XEq.of.All_XEqGetS.fin ?_
    intro i
    have hn : n = [n].prod := by simp
    rw [GetMul.eq.MulGetS.fin A.data c.data i, GetMul.eq.MulGetS.fin B.data c.data i]
    exact XEqMulS.of.XEq.Imp_XEqInvS
      (All_XEqGetS.of.XEq.fin (XEqDataS.of.XEq h) i)
      (h_xinfty (Fin.cast hn.symm i))
  exact XEqSumS.of.XEq.Ge_0 h_pos h_mul 0


private lemma get_dot
  (A : Tensor ℝ* [n]) (X : Tensor ℝ* [n, m]) (j : Fin m)
  (hj : j < (A @ X).length := by simp [matmul_shape]; grind) :
  (A @ X).get ⟨j, hj⟩ = A @ tensor_col X j := by
  simpa [tensor_col] using GetDot.eq.Dot_GetT.fin A X j hj


private lemma get_row
  (X : Tensor ℝ* [m, n]) (A : Tensor ℝ* [n]) (i : Fin m)
  (hi : i < (X @ A).length := by simp [matmul_shape]; grind) :
  (X @ A).get ⟨i, hi⟩ = (tensor_row X i) @ A := by
  convert GetDot.eq.DotGet.une X A i using 1
  simp [GetElem.getElem, tensor_row]


@[main]
private lemma main
  {A B : Tensor ℝ* [n]}
  {X : Tensor ℝ* [n, m]}
-- given
  (h_xinfty : ∀ j : Fin m, ∀ i : Fin n, ((tensor_col X j).data[i] → ∞) → A.data[i]⁻¹ ≈ B.data[i]⁻¹)
  (h_pos : ∀ j : Fin m, B * tensor_col X j ≥ 0)
  (h : A ≈ B) :
-- imply
  A @ X ≈ B @ X := by
-- proof
  apply XEq.of.All_XEqGetS.GtLength_0 (h := by simp [matmul_shape])
  intro j
  rw [get_dot A X j, get_dot B X j]
  exact dot_vec (h_xinfty j) (h_pos j) h


@[main]
private lemma left
  {A B : Tensor ℝ* [n]}
  {X : Tensor ℝ* [m, n]}
-- given
  (h_xinfty : ∀ i : Fin m, ∀ k : Fin n, ((tensor_row X i).data[k] → ∞) → A.data[k]⁻¹ ≈ B.data[k]⁻¹)
  (h_pos : ∀ i : Fin m, B * tensor_row X i ≥ 0)
  (h : A ≈ B) :
-- imply
  X @ A ≈ X @ B := by
  apply XEq.of.All_XEqGetS.GtLength_0 (h := by simp [matmul_shape])
  intro i
  rw [get_row X A i, get_row X B i]
  rw [Dot.comm, Dot.comm]
  exact dot_vec (h_xinfty i) (h_pos i) h


-- created on 2026-07-29
