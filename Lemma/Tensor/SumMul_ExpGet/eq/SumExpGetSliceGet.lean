import Lemma.Int.ToNatSubCoeS.eq.Sub
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Int.In_Ico.is.In_IcoToNatS
import Lemma.Int.InSub.is.In_Ico_AddS
import Lemma.Int.LtSub.is.Lt_Add
import Lemma.Int.Icc_Sub_1.eq.Ico
import Lemma.Int.InSub.is.In_Icc_AddS
import Lemma.Nat.CoeIte.eq.Ite_CoeS
import Lemma.Nat.MulIte.eq.Ite_MulS
import Lemma.Tensor.XEqDotS.of.XEq
import Lemma.Tensor.BandPart.eq.Stack_BoolIn_Icc
import Lemma.Tensor.Get.of.Eq
import Lemma.Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool
open Tensor Nat Int


@[main]
private lemma main
  [ExpPos α]
  [NeZero (l : ℕ)]
  [NeZero (u : ℕ)]
  [NeZero (n : ℕ)]
-- given
  (A : Tensor α [n, n])
  (i : Fin n) :
-- imply
  let Ξ := (1 : Tensor α [n, n]).band_part (l - 1) (u - 1)
  (Ξ[i] * exp A[i]).sum = (exp A[i, i + 1 - l : n ⊓ i + u]).sum := by
-- proof
  denote h_Ξ : Ξ = _
  have h_Ξᵢ := Get.of.Eq.fin h_Ξ i
  rw [BandPart.eq.Stack_BoolIn_Icc] at h_Ξᵢ
  rw [EqGetStack.fn.fin] at h_Ξᵢ
  simp only [Bool.Bool.eq.Ite] at h_Ξᵢ
  rw [CoeSub.eq.SubCoeS.of.Ge (by grind [NeZero.pos l])] at h_Ξᵢ
  rw [CoeSub.eq.SubCoeS.of.Ge (by grind [NeZero.pos u])] at h_Ξᵢ
  rw [NegSub.eq.Sub] at h_Ξᵢ
  conv_rhs at h_Ξᵢ =>
    arg 2
    ext j
    arg 1
    arg 1
    erw [Int.Icc_Sub_1.eq.Ico]
    rw [Int.InSub.is.In_Ico_AddS.left]
    rw [Add_Sub.eq.SubAdd]
    rw [In_Ico.is.In_IcoToNatS]
    rw [AddCoeS.eq.CoeAdd]
    rw [AddCoeS.eq.CoeAdd]
    rw [EqToNat]
    rw [ToNatSubCoeS.eq.Sub]
  simp [GetElem.getElem]
  rw [h_Ξᵢ]
  rw [Sum_0.eq.Sum_Get.fin]
  conv_lhs =>
    arg 2
    ext k
    erw [GetMul.eq.MulGetS.fin]
  conv_lhs =>
    arg 2
    ext k
    rw [EqGetStack.fn.fin]
    rw [Nat.CoeIte.eq.Ite_CoeS]
  conv_lhs =>
    arg 2
    ext k
    erw [Nat.MulIte.eq.Ite_MulS]
  conv_lhs =>
    arg 2
    ext k
    arg 2
    simp
    erw [EqMul1]
  conv_lhs =>
    arg 2
    ext k
    arg 3
    simp
    erw [Nat.EqMul0_0]
  conv_lhs =>
    arg 2
    ext k
    erw [GetExp.eq.ExpGet.fin]
  sorry


-- created on 2026-08-08
