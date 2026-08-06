import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Dot
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetDot.eq.Dot_GetT
import Lemma.Tensor.XEq.is.All_XEqGetS.of.GtLength_0
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Tensor.XEqSumS.of.XEq.OrAll_NotInfinite
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.XEq.is.All_XEqGetS
import Lemma.Hyperreal.XEqMulS.of.XEq.Imp_XEqInvS
open Tensor Hyperreal Vector
set_option maxHeartbeats 1000000


private lemma dot_vec
  {A B c : Tensor ℝ* [n]}
-- given
  (h_xinfty : ∀ i : Fin n, (c.data[i] → ∞) → A.data[i]⁻¹ ≈ B.data[i]⁻¹)
  (h_or :
    (∀ i : Fin n, ¬((B * c).data[i] → ∞)) ∨
    (B * c ≥ 0) ∨
    (B * c ≤ 0))
  (h : A ≈ B) :
-- imply
  A @ c ≈ B @ c := by
-- proof
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
  obtain h_fin | h_ge | h_le := h_or
  have hn : n = [n].prod := by simp
  ·
    exact XEqSumS.of.XEq.OrAll_NotInfinite
      (Or.inl fun i => h_fin (Fin.cast hn.symm i)) h_mul 0
  ·
    exact XEqSumS.of.XEq.OrAll_NotInfinite (Or.inr (Or.inl h_ge)) h_mul 0
  ·
    exact XEqSumS.of.XEq.OrAll_NotInfinite (Or.inr (Or.inr h_le)) h_mul 0


private lemma get_dot
-- given
  (A : Tensor ℝ* [n]) (X : Tensor ℝ* [n, m]) (j : Fin m)
  (hj : j < (A @ X).length := by simp [matmul_shape]; grind) :
-- imply
  (A @ X).get ⟨j, hj⟩ = A @ Xᵀ.get j := by
-- proof
  have h := GetDot.eq.Dot_GetT.fin A X j
  conv_lhs => simp [GetElem.getElem]
  exact h


private lemma get_row
-- given
  (X : Tensor ℝ* [m, n]) (A : Tensor ℝ* [n]) (i : Fin m)
  (hi : i < (X @ A).length := by simp [matmul_shape]; grind) :
-- imply
  (X @ A).get ⟨i, hi⟩ = (let row : Tensor ℝ* [n] := X[i]; row) @ A := by
-- proof
  convert GetDot.eq.DotGet.une X A i using 2
  · simp [GetElem.getElem]
  · rfl


@[main]
private lemma main
  {A B : Tensor ℝ* [n]}
  {X : Tensor ℝ* [n, m]}
-- given
  (h_xinfty : ∀ j : Fin m, ∀ i : Fin n,
    ((let col : Tensor ℝ* [n] := Xᵀ[j]; col).data[i] → ∞) → A.data[i]⁻¹ ≈ B.data[i]⁻¹)
  (h_or : ∀ j : Fin m,
    (∀ i : Fin n, ¬((B * (let col : Tensor ℝ* [n] := Xᵀ[j]; col)).data[i] → ∞)) ∨
    (B * (let col : Tensor ℝ* [n] := Xᵀ[j]; col) ≥ 0) ∨
    (B * (let col : Tensor ℝ* [n] := Xᵀ[j]; col) ≤ 0))
  (h : A ≈ B) :
-- imply
  A @ X ≈ B @ X := by
-- proof
  apply XEq.of.All_XEqGetS.GtLength_0 (h := by simp [matmul_shape])
  intro j
  rw [get_dot A X j, get_dot B X j]
  conv_lhs => simp [GetElem.getElem]
  conv_rhs => simp [GetElem.getElem]
  exact dot_vec (h_xinfty j) (h_or j) h


@[main]
private lemma left
  {A B : Tensor ℝ* [n]}
  {X : Tensor ℝ* [m, n]}
-- given
  (h_xinfty : ∀ i : Fin m, ∀ k : Fin n,
    ((let row : Tensor ℝ* [n] := X[i]; row).data[k] → ∞) → A.data[k]⁻¹ ≈ B.data[k]⁻¹)
  (h_or : ∀ i : Fin m,
    (∀ k : Fin n, ¬((B * (let row : Tensor ℝ* [n] := X[i]; row)).data[k] → ∞)) ∨
    (B * (let row : Tensor ℝ* [n] := X[i]; row) ≥ 0) ∨
    (B * (let row : Tensor ℝ* [n] := X[i]; row) ≤ 0))
  (h : A ≈ B) :
-- imply
  X @ A ≈ X @ B := by
-- proof
  apply XEq.of.All_XEqGetS.GtLength_0 (h := by simp [matmul_shape])
  intro i
  rw [get_row X A i, get_row X B i]
  rw [Dot.comm]
  conv_rhs => rw [Dot.comm]
  exact dot_vec (h_xinfty i) (h_or i) h


-- created on 2026-07-29
