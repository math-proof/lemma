import Lemma.Hyperreal.XEqMulS.of.XEq.Imp_XEqInvS
import Lemma.Nat.Mul
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Dot
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Tensor.XEqSumS.of.XEq.Ge_0
import Lemma.Vector.GetMul.eq.MulGetS
open Hyperreal Nat Tensor Vector


@[main]
private lemma main
  {A B X : Tensor ℝ* [n]}
-- given
  (h_xinfty : ∀ i : Fin n, (X.data[i] → ∞) → A.data[i]⁻¹ ≈ B.data[i]⁻¹)
  (h_pos : B * X ≥ 0)
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
  exact XEqSumS.of.XEq.Ge_0 h_pos h_mul 0


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
  apply main h_xinfty _ h
  rwa [← Mul.comm X B]


-- created on 2026-07-29
