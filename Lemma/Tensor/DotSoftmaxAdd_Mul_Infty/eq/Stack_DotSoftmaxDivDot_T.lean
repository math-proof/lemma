import Lemma.Tensor.SEqSoftmaxS.of.SEq.Eq
import Lemma.List.EqSwap_0'1
import Lemma.Nat.CoeAdd_1.eq.AddCoe_1
import Lemma.Tensor.Dot.eq.Bmm
import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_SoftmaxGetSlice
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.GetDot.eq.DotGetS
import Lemma.Tensor.GetDot_TGetSlice.as.Dot_Get
import Lemma.Tensor.GetSliceGetDiv.eq.DivGetSliceGet
import Lemma.Tensor.GetTCast_T.eq.Get
import Lemma.Tensor.MapBmm.eq.BmmMapS.of.All_Eq_Add.All_Eq_Mul
import Lemma.Tensor.MapCast.as.Map.of.Eq
import Lemma.Tensor.MapDiv.eq.DivMap.of.All_Eq_Div
import Lemma.Tensor.TMap.eq.MapT
import Lemma.Tensor.XEq.of.Eq
open List Nat Tensor
set_option maxHeartbeats 500000


@[main]
private lemma gpt
  [NeZero (n : ℕ)]
  {d_z : ℕ}
-- given
  (Q K V : Tensor ℝ [n, d_z]) :
-- imply
  let Q : Tensor ℝ* [n, d_z] := Q
  let K : Tensor ℝ* [n, d_z] := K
  let V : Tensor ℝ* [n, d_z] := V
  let QK : Tensor ℝ* [n, n] := Q @ Kᵀ
  (QK / √(d_z : ℝ*) + ((1 : Tensor ℝ* [n, n]).band_part n 0 - 1) * ∞).softmax @ V ≈ [i < n] (Q[i] @ K[:i + 1]ᵀ / √(d_z : ℝ*)).softmax @ V[:i + 1] := by
-- proof
  extract_lets Q' K' V' QK'
  let KT := cast (congrArg (Tensor ℝ) (EqSwap_0'1 n d_z)) Kᵀ
  let A : Tensor ℝ [n, n] := (Q @ KT) / √(d_z : ℝ)
  have hKT : (KT : Tensor ℝ* [d_z, n]) = cast (congrArg (Tensor ℝ*) (EqSwap_0'1 n d_z)) (K : Tensor ℝ* [n, d_z])ᵀ := by
    simp only [KT]
    rw [MapCast.eq.Cast_Map.of.Eq (EqSwap_0'1 n d_z)]
    rw [TMap.eq.MapT]
    rfl
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
  refine (XEq.of.Eq ?lhs).trans ((DotSoftmaxAdd_Mul_Infty.eq.Stack_SoftmaxGetSlice A V).trans (XEq.of.Eq ?rhs))
  ·
    simp only [hdiv]
    rfl
  ·
    apply Eq.of.All_EqGetS.fin
    intro i
    simp [EqGetStack.fin]
    simp only [V']
    apply Bool.Eq.of.SEq
    apply SEqDotS.of.SEq
    apply SEqSoftmaxS.of.SEq.Eq (by simp [matmul_shape, EqSwap_0'1])
    apply Bool.SEq.of.Eq
    rw [← hdiv, hQK]
    simp [GetElem.getElem]
    erw [GetSliceGetDiv.eq.DivGetSliceGet.fin ((Q : Tensor ℝ* [n, d_z]) @ (KT : Tensor ℝ* [d_z, n])) (√(d_z : ℝ*)) i]
    apply congrArg (α := Tensor ℝ* ((⟨0, ((i : ℕ) : ℤ) + 1, 1⟩ : Slice).length n :: [])) (fun t => t / √(d_z : ℝ*))
    rw [AddCoe_1.eq.CoeAdd_1]
    apply Eq.of.All_EqGetS.fin
    intro j
    apply (GetGetSlice.eq.Get.fin (X := ((Q : Tensor ℝ* [n, d_z]) @ (KT : Tensor ℝ* [d_z, n]))[i]) (n := (i : ℕ) + 1) j).trans
    have h_j := j.isLt
    simp only [List.LengthSlice.eq.Min] at h_j
    apply (congrArg (((Q : Tensor ℝ* [n, d_z]) @ (KT : Tensor ℝ* [d_z, n]))[i]).get (Fin.ext rfl)).trans
    trans id (α := Tensor ℝ* (matmul_shape [n, d_z] [d_z, n]).tail.tail) (((Q : Tensor ℝ* [n, d_z]).get i) @ (K : Tensor ℝ* [n, d_z]).get ⟨j, by grind⟩)
    ·
      simp [GetElem.getElem]
      erw [GetDot.eq.DotGetS.fin]
      rw [congrArg (·ᵀ) hKT]
      apply congrArg
      apply GetTCast_T.eq.Get.fin
    ·
      apply Eq.symm
      apply Bool.Eq.of.SEq
      apply GetDot_TGetSlice.as.Dot_Get.fin


-- created on 2023-06-18
-- updated on 2026-08-20
