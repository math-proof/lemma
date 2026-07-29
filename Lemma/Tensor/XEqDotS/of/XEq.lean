import Lemma.Hyperreal.XEqMulS.of.XEq.XEq.ImpOrInfinitesimalS
import Lemma.Tensor.DataMul.eq.Mul_Data
import Lemma.Tensor.Einsum.eq.MulGetData_0
import Lemma.Tensor.Einsum.eq.MulDataS_Get_0
import Lemma.Tensor.XEq.is.All_XEqGetS
import Lemma.Tensor.XEq.is.XEqDataS
import sympy.tensor.tensor
open Tensor Hyperreal


private lemma mulGetData_0
  {A B : Tensor ℝ* []}
  (h : A ≈ B)
  (X : Tensor ℝ* s_X) :
  A @ X ≈ B @ X := by
  rw [Einsum.eq.MulGetData_0, Einsum.eq.MulGetData_0]
  apply XEq.of.XEqDataS
  rw [DataMul.eq.Mul_Data, DataMul.eq.Mul_Data]
  have h₀ := XEqDataS.of.XEq h
  simp at h₀
  refine Vector.XEq.of.All_XEqGetS.fin ?_
  intro i
  by_cases hx : X.data[i] → 0
  · by_cases hb : B.data[0] → 0
    · exact XEqMulS.of.XEq.XEq.ImpOrInfinitesimalS (fun h =>
        rcases h with hb' | hx'
        · exact ⟨hb', hx⟩
        · exact ⟨hb, hx'⟩) h₀ (Setoid.refl _)
    · grind
  · exact XEqMulS.of.XEq.XEq.ImpOrInfinitesimalS (fun h_ant =>
      absurd h_ant (by simpa using hx)) h₀ (Setoid.refl _)


private lemma getData_0_mul
  {A B : Tensor ℝ* []}
  (h : A ≈ B)
  (X : Tensor ℝ* s_X) :
  X @ A ≈ X @ B := by
  rw [Einsum.eq.MulDataS_Get_0, Einsum.eq.MulDataS_Get_0]
  apply XEq.of.XEqDataS
  rw [DataMul.eq.Mul_Data, DataMul.eq.Mul_Data]
  have h₀ := XEqDataS.of.XEq h
  simp at h₀
  refine Vector.XEq.of.All_XEqGetS.fin ?_
  intro i
  by_cases hx : X.data[i] → 0
  · by_cases hb : B.data[0] → 0
    · exact XEqMulS.of.XEq.XEq.ImpOrInfinitesimalS (fun h =>
        rcases h with hb' | hx'
        · exact ⟨hb', hx⟩
        · exact ⟨hb, hx'⟩) (Setoid.refl _) h₀
    · grind
  · exact XEqMulS.of.XEq.XEq.ImpOrInfinitesimalS (fun h_ant =>
      absurd h_ant (by simpa using hx)) (Setoid.refl _) h₀


@[main]
private lemma main
  {A B : Tensor ℝ* s}
-- given
  (h : A ≈ B)
  (X : Tensor ℝ* s_X) :
-- imply
  A @ X ≈ B @ X := by
-- proof
  match s with
  | [] =>
    exact mulGetData_0 h X
  | _ :: _ =>
    apply @Tensor.XEq.of.All_XEqGetS.GtLength_0 (h := by simp)
    intro i
    sorry


@[main]
private lemma left
  {A B : Tensor ℝ* s}
-- given
  (h : A ≈ B)
  (X : Tensor ℝ* s_X) :
-- imply
  X @ A ≈ X @ B := by
-- proof
  match s with
  | [] =>
    exact getData_0_mul h X
  | _ :: _ =>
    apply @Tensor.XEq.of.All_XEqGetS.GtLength_0 (h := by simp)
    intro i
    sorry


-- created on 2026-07-29
