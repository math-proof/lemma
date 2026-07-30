import Lemma.Tensor.XEq.of.Eq
import Lemma.Tensor.GtExp_0
import Lemma.Tensor.Lt0Get.of.Gt_0
import Lemma.Tensor.Lt0SumGetBandPart
import Lemma.Tensor.Lt0SumMul.of.GtSum_0.Ge_0.Gt_0
import Lemma.Tensor.GtSumData_0.is.GtSum_0
import Lemma.Hyperreal.Eq_0.of.Infinitesimal
import Lemma.Vector.MapSum.eq.SumMap.of.All_EqUFnAdd
import Lemma.Tensor.MapData.eq.DataMap
import Lemma.Tensor.MapBandPart.eq.BandPartMap.of.EqUFn0'0
import Lemma.Tensor.MapMul.eq.MulMapS.of.All_Eq_Mul
import Lemma.Tensor.Eq1Coe1
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.MapExp.eq.ExpMap.of.All_EqUFnExp_ExpUFn
import Lemma.Tensor.Le0Get.of.Ge_0
import Lemma.Tensor.Le0BandPart
import Lemma.Tensor.Le0Stack.of.All_Ge_0
import Lemma.Tensor.GeExp_0
import Lemma.Tensor.Le0Mul.of.Ge_0.Ge_0
import Lemma.Tensor.XEqDivS_Sum_0.of.XEq.NotInfinitesimalSum.Ge_0
import Lemma.Tensor.Div_KeepdimSum.eq.Div_Sum
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
import sympy.functions.elementary.exponential
open Tensor Hyperreal
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
  have h_band_part := BandPart.eq.Stack_BoolIn_Icc n n (l - 1) (u - 1) (α := ℝ*)
  have h_Ξ := ExpAdd_MulInfty.eq.Mul_Stack_Bool (fun i j => ((j - i : ℤ) ∈ Icc (-(l - 1 : ℕ) : ℤ) (u - 1 : ℕ) : Bool)) A
  erw [← h_band_part] at h_Ξ
  rw [← h_A'] at h_Ξ
  simp [← h_Ξ_def] at h_Ξ
  denote h_a' : a' = (A' + (Ξ - 1) * ∞)
  rw [← h_a'] at h_Ξ ⊢
  denote h_z : z = a'.softmax @ V'
  rw [← h_z]
  apply @Tensor.XEq.of.All_XEqGetS.fin
  intro i
  have h_Ξᵢ := XEqGetS.of.XEq.GtLength.fin (i := i) (by grind) h_Ξ
  simp at h_Ξᵢ
  rw [@Tensor.GetMul.eq.MulGetS.fin] at h_Ξᵢ
  have h_zi := Get.of.Eq.fin h_z i
  simp at h_zi
  rw [Softmax.eq.DivExp_KeepdimSumExp] at h_zi
  have := GetDot.eq.DotGet.fin (exp a' / ((exp a').sum 1).keepdim) V' i
  simp at this
  have h_zi := h_zi.trans this
  conv_rhs at h_zi => erw [@Tensor.GetDiv.eq.DivGetS.fin]
  simp at h_zi
  have := GetKeepdim.eq.KeepdimCast_Get.of.GtGet_0.Gt_0.GtLength
    (i := i)
    (by grind) (by grind) (by grind)
    ((exp a').sum 1)
  simp at this
  rw [this] at h_zi
  erw [GetSum.eq.Cast_SumGet.of.GtGet_0.LtAdd_1Length.fin (d := 0) (by grind) (by grind)] at h_zi
  simp at h_zi
  erw [Div_KeepdimSum.eq.Div_Sum] at h_zi
  have h_Ξᵢ : (exp a').get i / (let den : Tensor ℝ* [] := ((exp a').get i).sum 0; den) ≈ (exp A').get i * Ξ.get i / (let den : Tensor ℝ* [] := ((exp A').get i * Ξ.get i).sum 0; den) := by
    simp
    apply XEqDivS_Sum_0.of.XEq.NotInfinitesimalSum.Ge_0 _ _ h_Ξᵢ
    .
      apply Le0Mul.of.Ge_0.Ge_0
      .
        erw [GetExp.eq.ExpGet.fin (i := ⟨i, by grind⟩)]
        simp
        apply GeExp_0
      .
        apply Le0Get.of.Ge_0
        apply Le0BandPart
    .
      dsimp [A']
      rw [ExpMap.eq.MapExp.of.All_EqUFnExp_ExpUFn (by aesop)]
      erw [GetMap.eq.MapGet.fin]
      have hΞ : Ξ = (1 : Tensor ℝ [n, n]).band_part (l - 1) (u - 1) := by
        simp [Ξ]
        erw [Eq1Coe1]
        rw [MapBandPart.eq.BandPartMap.of.EqUFn0'0]
        rfl
      rw [hΞ]
      conv =>
        pattern (map _ _).get _
        erw [GetMap.eq.MapGet.fin]
      erw [MulMapS.eq.MapMul.of.All_Eq_Mul (by aesop)]
      rw [DataMap.eq.MapData]
      erw [Vector.SumMap.eq.MapSum.of.All_EqUFnAdd (by aesop)]
      apply NotInfinitesimal.of.Ne_0
      apply Nat.Ne.of.Gt
      apply GtSumData_0.of.GtSum_0
      apply Lt0SumMul.of.GtSum_0.Ge_0.Gt_0
      .
        apply Lt0Get.of.Gt_0
        apply GtExp_0
      .
        apply Le0Get.of.Ge_0
        apply Le0BandPart
      .
        apply Lt0SumGetBandPart
  have h_zi := Tensor.XEq.of.Eq h_zi
  have h_xeq : ((Exp.exp a').get i / (let den : Tensor ℝ* [] := ((Exp.exp a').get i).sum 0; den)) @ V' ≈ ((exp A').get i * Ξ.get i / (let den : Tensor ℝ* [] := ((exp A').get i * Ξ.get i).sum 0; den)) @ V' := by
    simp
    sorry
  -- rw [EqGetStack.fn.fin]
  let band_A := A'[i, i + 1 - l : n ⊓ i + u]
  let band_V := V'[i + 1 - l:n ⊓ i + u]
  sorry


-- created on 2026-01-02
-- updated on 2026-07-21
