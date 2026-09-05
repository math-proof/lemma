import Lemma.Tensor.SEqSoftmaxS.of.SEq.Eq
import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax
import Lemma.Tensor.GetDot_TGetSlice.as.Dot_Get
import Lemma.Tensor.GetSliceGetDiv.eq.DivGetSliceGet
import Lemma.Tensor.GetTCast_T.eq.Get
import Lemma.Tensor.MapBmm.eq.BmmMapS.of.All_Eq_Add.All_Eq_Mul
import Lemma.Tensor.MapDiv.eq.DivMap.of.All_Eq_Div
open Tensor
set_option maxHeartbeats 2000000


@[main]
private lemma gpt
  [NeZero (l : ℕ)]
  {n : ℕ}
  {d_z : ℕ}
-- given
  (Q K V : Tensor ℝ [n, d_z]) :
-- imply
  let Q : Tensor ℝ* [n, d_z] := Q
  let K : Tensor ℝ* [n, d_z] := K
  let V : Tensor ℝ* [n, d_z] := V
  let QK : Tensor ℝ* [n, n] := Q @ Kᵀ
  (QK / √(d_z : ℝ*) + ((1 : Tensor ℝ* [n, n]).band_part (l - 1) 0 - 1) * ∞).softmax @ V ≈ [i < n] (Q[i] @ K[(i + 1 - l : ℕ):(i + 1 : ℕ)]ᵀ / √(d_z : ℝ*)).softmax @ V[(i + 1 - l : ℕ):(i + 1 : ℕ)] := by
-- proof
  extract_lets Q' K' V' QK'
  let KT := cast (congrArg (Tensor ℝ) (List.EqSwap_0'1 n d_z)) Kᵀ
  let A : Tensor ℝ [n, n] := (Q @ KT) / √(d_z : ℝ)
  have hKT : (KT : Tensor ℝ* [d_z, n]) = cast (congrArg (Tensor ℝ*) (List.EqSwap_0'1 n d_z)) (K : Tensor ℝ* [n, d_z])ᵀ := by
    simp only [KT]
    rw [MapCast.eq.Cast_Map.of.Eq (List.EqSwap_0'1 n d_z)]
    rw [TMap.eq.MapT]
  have hQK : QK' = (Q : Tensor ℝ* [n, d_z]) @ (KT : Tensor ℝ* [d_z, n]) := by
    apply Eq.of.EqDataS
    simp only [QK', Q', K', KT, hKT]
    rfl
  have hdiv : QK' / √(d_z : ℝ*) = (A : Tensor ℝ* [n, n]) := by
    rw [hQK]
    simp only [A]
    conv_rhs => erw [MapDiv.eq.DivMap.of.All_Eq_Div (by aesop)]
    apply congrArg (α := Tensor ℝ* [n, n]) (fun t => t / √(d_z : ℝ*))
    simp [Dot.eq.Bmm]
    apply BmmMapS.eq.MapBmm.of.All_Eq_Add.All_Eq_Mul <;> aesop
  apply (XEq.of.Eq _).trans ((DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax (l := l) (u := 1) A V).trans (XEq.of.Eq _))
  ·
    simp only [hdiv]
    rfl
  ·
    apply Eq.of.All_EqGetS.fin
    intro i
    conv_lhs => erw [EqGetStack.fin]
    conv_rhs => erw [EqGetStack.fin]
    simp only [V']
    apply Bool.Eq.of.SEq
    apply SEqDotS.of.SEq
    apply SEqSoftmaxS.of.SEq.Eq (by simp [matmul_shape])
    apply Bool.SEq.of.Eq
    rw [← hdiv, hQK]
    simp [GetElem.getElem]
    erw [GetSliceGetDiv.eq.DivGetSliceGet.fin ((Q : Tensor ℝ* [n, d_z]) @ (KT : Tensor ℝ* [d_z, n])) (√(d_z : ℝ*)) i (i + 1 - l) (i + 1)]
    apply congrArg (α := Tensor ℝ* ((⟨(i + 1 - l : ℕ), (i + 1 : ℕ), 1⟩ : Slice).length n :: [])) (fun t => t / √(d_z : ℝ*))
    apply Eq.of.All_EqGetS.fin
    intro j
    have h_j := j.isLt
    simp only [List.LengthSlice.eq.SubMin] at h_j
    apply (GetGetSlice.eq.Get_Add.of.GtSubMin.fin h_j (X := ((Q : Tensor ℝ* [n, d_z]) @ (KT : Tensor ℝ* [d_z, n]))[i])).trans
    apply Eq.trans (b := (((Q : Tensor ℝ* [n, d_z]).get i) @ (K : Tensor ℝ* [n, d_z]).get ⟨i + 1 - l + j, by grind⟩))
    ·
      simp [GetElem.getElem]
      erw [GetDot.eq.DotGetS.fin]
      rw [congrArg T hKT]
      apply congrArg
      apply GetTCast_T.eq.Get.fin
    ·
      apply Eq.symm
      apply Bool.Eq.of.SEq
      apply GetDot_TGetSlice.as.Dot_Get.fin


-- created on 2023-06-18
-- updated on 2026-08-20
