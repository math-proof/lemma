import Lemma.Hyperreal.XEqMulS.of.XEq.Imp_XEqInvS
import Lemma.Nat.Mul
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Dot
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Tensor.XEqSumS.of.XEq.OrAll_NotInfinite
import Lemma.Vector.GetMul.eq.MulGetS
open Hyperreal Nat Tensor Vector


@[main]
private lemma main
  {A B X : Tensor ℝ* [n]}
-- given
  (h_xinfty : ∀ i : Fin n, (X.data[i] → ∞) → A.data[i]⁻¹ ≈ B.data[i]⁻¹)
  (h_or :
    (∀ i : Fin n, ¬((B * X).data[i] → ∞)) ∨
    (B * X ≥ 0) ∨
    (B * X ≤ 0))
  (h : A ≈ B) :
-- imply
  A @ X ≈ B @ X := by
-- proof
  rw [Dot.eq.SumMul__0, Dot.eq.SumMul__0]
  have h_mul : A * X ≈ B * X := by
    apply XEq.of.XEqDataS
    rw [DataMul.eq.MulDataS, DataMul.eq.MulDataS]
    refine Vector.XEq.of.All_XEqGetS.fin ?_
    intro i
    have hn : n = [n].prod := by simp
    rw [GetMul.eq.MulGetS.fin A.data X.data i, GetMul.eq.MulGetS.fin B.data X.data i]
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


@[main]
private lemma left
  {A B X : Tensor ℝ* [n]}
-- given
  (h_xinfty : ∀ i : Fin n, (X.data[i] → ∞) → A.data[i]⁻¹ ≈ B.data[i]⁻¹)
  (h_pos : X * B ≥ 0)
  (h : A ≈ B) :
-- imply
  X @ A ≈ X @ B := by
-- proof
  rw [Dot.comm]
  conv_rhs =>
    rw [Dot.comm]
  apply main h_xinfty (Or.inr (Or.inl (by rw [Mul.comm]; exact h_pos))) h


-- created on 2026-07-29
