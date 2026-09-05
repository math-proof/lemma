import Lemma.Nat.Mul
import Lemma.Tensor.Dot
import Lemma.Tensor.Dot.eq.TensorDotDataS
import Lemma.Tensor.Ge0Mul.is.Ge0MulDataS
import Lemma.Tensor.Le0Mul.is.Le0MulDataS
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Vector.XEqDotS.of.XEq.OrAll_NotInfinite.All_Imp_XEqInvS
open Nat Tensor Vector


@[main]
private lemma main
  {A B C : Tensor ℝ* [n]}
-- given
  (h_xinfty : ∀ i : Fin n, (C.data[i] → ∞) → A.data[i]⁻¹ ≈ B.data[i]⁻¹)
  (h_or : (∀ i : Fin n, ¬((B * C).data[i] → ∞)) ∨ B * C ≥ 0 ∨ B * C ≤ 0)
  (h : A ≈ B) :
-- imply
  A @ C ≈ B @ C := by
-- proof
  rw [Dot.eq.TensorDotDataS, Dot.eq.TensorDotDataS]
  apply XEq.of.XEqDataS
  apply XEq.of.All_XEqGetS.fin
  intro i
  fin_cases i
  apply XEqDotS.of.XEq.OrAll_NotInfinite.All_Imp_XEqInvS (fun i h_inf => h_xinfty ⟨i, by grind⟩ h_inf) _ (XEqDataS.of.XEq h)
  obtain h_fin | h_ge | h_le := h_or
  ·
    refine Or.inl fun i hi => h_fin ⟨i, by grind⟩ ?_
    simpa [DataMul.eq.MulDataS]
  ·
    exact Or.inr (Or.inl (Le0MulDataS.of.Le0Mul h_ge))
  ·
    exact Or.inr (Or.inr (Ge0MulDataS.of.Ge0Mul h_le))


@[main]
private lemma left
  {A B C : Tensor ℝ* [n]}
-- given
  (h_xinfty : ∀ i : Fin n, (C.data[i] → ∞) → A.data[i]⁻¹ ≈ B.data[i]⁻¹)
  (h_or : (∀ i : Fin n, ¬((C * B).data[i] → ∞)) ∨ C * B ≥ 0 ∨ C * B ≤ 0)
  (h : A ≈ B) :
-- imply
  C @ A ≈ C @ B := by
-- proof
  rw [Tensor.Dot.comm]
  conv_rhs => rw [Tensor.Dot.comm]
  rw [Mul.comm] at h_or
  apply main h_xinfty h_or h


-- created on 2026-07-29
-- updated on 2026-09-05
