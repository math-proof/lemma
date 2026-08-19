import Lemma.Bool.Bool.eq.Ite
import Lemma.Nat.Mul_Ite.eq.Ite_MulS
import Lemma.Int.Icc_Sub_1.eq.Ico
import Lemma.Int.InSub.is.In_Ico_AddS
import Lemma.Int.In_Ico.is.In_IcoToNatS
import Lemma.Int.ToNatSubCoeS.eq.Sub
import Lemma.Nat.CoeIte.eq.Ite_CoeS
import Lemma.Nat.EqMul_0'0
import Lemma.Nat.EqMul_1
import Lemma.Tensor.BandPart.eq.Stack_BoolIn_Icc
import Lemma.Tensor.Get.of.Eq
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.Sum_IteIn_Ico.eq.SumGetSlice
open Int Nat Tensor


@[main, fin]
private lemma main
  [Semiring α]
  [NeZero (l : ℕ)]
  [NeZero (u : ℕ)]
  [NeZero (n : ℕ)]
-- given
  (A : Tensor α [n, n])
  (i : Fin n) :
-- imply
  let Ξ := (1 : Tensor α [n, n]).band_part (l - 1) (u - 1)
  (A[i] * Ξ[i]).sum = A[i][(i + 1 - l : ℕ):(i + u : ℕ)].sum := by
-- proof
  denote h_Ξ : Ξ = _
  have h_Ξᵢ := Get.of.Eq.fin h_Ξ i
  rw [BandPart.eq.Stack_BoolIn_Icc] at h_Ξᵢ
  rw [EqGetStack.fin] at h_Ξᵢ
  simp only [Bool.Bool.eq.Ite] at h_Ξᵢ
  rw [CoeSub.eq.SubCoeS.of.Ge (by grind [NeZero.pos l])] at h_Ξᵢ
  rw [CoeSub.eq.SubCoeS.of.Ge (by grind [NeZero.pos u])] at h_Ξᵢ
  rw [NegSub.eq.Sub] at h_Ξᵢ
  conv_rhs at h_Ξᵢ =>
    arg 2
    ext j
    arg 1
    arg 1
    erw [Icc_Sub_1.eq.Ico]
    rw [InSub.is.In_Ico_AddS.left]
    rw [Add_Sub.eq.SubAdd]
    rw [In_Ico.is.In_IcoToNatS]
    rw [Nat.AddCoeS.eq.CoeAdd]
    rw [Nat.AddCoeS.eq.CoeAdd]
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
    rw [EqGetStack.fin]
    rw [CoeIte.eq.Ite_CoeS]
  conv_lhs =>
    arg 2
    ext k
    erw [Mul_Ite.eq.Ite_MulS]
  conv_lhs =>
    arg 2
    ext k
    arg 2
    simp
    erw [EqMul_1]
  conv_lhs =>
    arg 2
    ext k
    arg 3
    simp
    erw [EqMul_0'0]
  erw [Sum_IteIn_Ico.eq.SumGetSlice.fin]
  rfl


-- created on 2026-08-11
-- updated on 2026-08-14
