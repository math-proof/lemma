import Lemma.Hyperreal.XEqMulS.of.XEq.ImpOrInfinitesimalS
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Dot
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Tensor.XEqSumS.of.XEq.Ge_0
import Lemma.Vector.GetMul.eq.MulGetS
open Hyperreal Tensor Vector


@[main]
private lemma main
  {A B X : Tensor ℝ* [n]}
-- given
  (h_or : ∀ i : Fin n, ((B.data[i] → 0) ∨ X.data[i] → 0) → ((B.data[i] → 0) ∧ X.data[i] → 0))
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
    exact XEqMulS.of.XEq.ImpOrInfinitesimalS (h_or (Fin.cast hn.symm i)) (All_XEqGetS.of.XEq.fin (XEqDataS.of.XEq h) i)
  exact XEqSumS.of.XEq.Ge_0 h_pos h_mul 0


@[main]
private lemma left
  {A B X : Tensor ℝ* [n]}
-- given
  (h_or : ∀ i : Fin n, ((X.data[i] → 0) ∨ B.data[i] → 0) → ((X.data[i] → 0) ∧ B.data[i] → 0))
  (h_pos : X * B ≥ 0)
  (h : A ≈ B) :
-- imply
  X @ A ≈ X @ B := by
-- proof
  simp_rw [And.comm, Or.comm] at h_or
  rw [Dot.comm]
  conv_rhs =>
    rw [Dot.comm]
  exact main h_or (by rwa [← Mul.comm X B]) h


-- created on 2026-07-29
