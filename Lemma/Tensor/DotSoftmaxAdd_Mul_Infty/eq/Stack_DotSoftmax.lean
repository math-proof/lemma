import Lemma.Tensor.BandPart.eq.Stack_BoolIn_Icc
import Lemma.Tensor.Get.of.Eq
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool
import Lemma.Tensor.GetDiv.eq.DivGetS
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetKeepdim.eq.KeepdimCast_Get.of.GtGet_0.Gt_0.GtLength
import Lemma.Tensor.GetSum.as.SumGet.of.GtGet_0.LtAdd_1Length
import Lemma.Tensor.XEq.is.All_XEqGetS
import Lemma.Tensor.Softmax.eq.DivExp_KeepdimSumExp
import Lemma.Tensor.XEqGetS.of.XEq.GtLength
open Tensor
set_option maxHeartbeats 1000000


@[main]
private lemma main
  [NeZero (l : ℕ)]
  [NeZero (u : ℕ)]
  [NeZero (n : ℕ)]
  [NeZero (d_z : ℕ)]
-- given
  (A : Tensor ℝ [n, n])
  (V : Tensor ℝ [n, d_z]) :
-- imply
  let Ξ := (1 : Tensor ℝ* [n, n]).band_part (l - 1) (u - 1)
  let A : Tensor ℝ* [n, n] := A
  let V : Tensor ℝ* [n, d_z] := V
  (A + (Ξ - 1) * ∞).softmax @ V ≈ [i < n] A[i, i + 1 - l : n ⊓ i + u].softmax @ V[i + 1 - l:n ⊓ i + u] := by
-- proof
  denote h_Ξ_def : Ξ = _
  denote h_A' : A' = _
  denote h_V' : V' = _
  have h_band_part := BandPart.eq.Stack_BoolIn_Icc n (l - 1) (u - 1) (α := ℝ*)
  have h_Ξ := ExpAdd_MulInfty.eq.Mul_Stack_Bool (fun i j => ((j - i : ℤ) ∈ Icc (-(l - 1 : ℕ) : ℤ) (u - 1 : ℕ) : Bool)) A
  erw [← h_band_part] at h_Ξ
  simp [← h_A', ← h_Ξ_def] at h_Ξ
  denote h_a' : a' = (A' + (Ξ - 1) * ∞)
  rw [← h_a'] at h_Ξ ⊢
  denote h_z : z = a'.softmax @ V'
  rw [← h_z]
  apply XEq.of.All_XEqGetS.fin
  intro i
  have h_Ξᵢ := XEqGetS.of.XEq.GtLength.fin (i := i) (by grind) h_Ξ
  simp at h_Ξᵢ
  rw [GetMul.eq.MulGetS.fin] at h_Ξᵢ
  have h_zi := Get.of.Eq.fin h_z i
  simp at h_zi
  rw [Softmax.eq.DivExp_KeepdimSumExp] at h_zi
  have := GetDot.eq.DotGet.fin (exp a' / ((exp a').sum 1).keepdim) V' i
  simp at this
  have h_zi := h_zi.trans this
  conv_rhs at h_zi => erw [GetDiv.eq.DivGetS.fin]
  simp at h_zi
  have := GetKeepdim.eq.KeepdimCast_Get.of.GtGet_0.Gt_0.GtLength
    (i := i)
    (by grind) (by grind) (by grind)
    ((exp a').sum 1)
  simp at this
  rw [this] at h_zi
  erw [GetSum.eq.Cast_SumGet.of.GtGet_0.LtAdd_1Length.fin (d := 0) (by grind) (by grind)] at h_zi
  simp at h_zi
  erw [h_Ξᵢ] at h_zi
  conv_lhs => erw [h_zi]
  rw [EqGetStack.fn.fin]
  let band_A := A'[i, i + 1 - l : n ⊓ i + u]
  let band_V := V'[i + 1 - l:n ⊓ i + u]
  sorry


-- created on 2026-01-02
-- updated on 2026-07-21
