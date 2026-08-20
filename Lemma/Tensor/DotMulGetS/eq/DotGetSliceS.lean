import Lemma.Bool.Bool.eq.Ite
import Lemma.Fin.Sum.of.All_Eq
import Lemma.Int.EqToNat
import Lemma.Int.Icc_Sub_1.eq.Ico
import Lemma.Int.InSub.is.In_Ico_AddS
import Lemma.Int.In_Ico.is.In_IcoToNatS
import Lemma.Int.Sub.eq.NegSub
import Lemma.Int.SubAdd.eq.Add_Sub
import Lemma.Int.ToNatSubCoeS.eq.Sub
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Nat.CoeIte.eq.Ite_CoeS
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.EqMul0_0
import Lemma.Nat.EqMul_0'0
import Lemma.Nat.EqMul_1
import Lemma.Nat.Mul_Ite.eq.Ite_MulS
import Lemma.Tensor.BandPart.eq.Stack_BoolIn_Icc
import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Get.of.Eq
import Lemma.Tensor.GetGetSlice.eq.Get_Add.of.GtSubMin
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.Sum_0.eq.Sum_Get
import Lemma.Tensor.Sum_IteIn_Ico.eq.SumGetSlice
open Int List Nat Tensor
set_option maxHeartbeats 1000000


@[main, fin]
private lemma main
  [Semiring α]
  [NeZero (l : ℕ)]
  [NeZero (u : ℕ)]
-- given
  (A : Tensor α [n, n])
  (V : Tensor α [n, k])
  (i : Fin n) :
-- imply
  let Ξ := (1 : Tensor α [n, n]).band_part (l - 1) (u - 1)
  (A[i] * Ξ[i]) @ V = A[i, (i + 1 - l : ℕ):(i + u : ℕ)] @ V[(i + 1 - l : ℕ):(i + u : ℕ)] := by
-- proof
  denote h_Ξ : Ξ = _
  let Ai : Tensor α [n] := A[i]
  let Ξi : Tensor α [n] := Ξ[i]
  change (Ai * Ξi) @ V = Ai[(i + 1 - l : ℕ):(i + u : ℕ)] @ V[(i + 1 - l : ℕ):(i + u : ℕ)]
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
  conv_lhs => erw [Dot.eq.Stack_Sum_MulGetS.une]
  conv_rhs => erw [Dot.eq.Stack_Sum_MulGetS.une]
  apply Eq.of.All_EqGetS.fin
  intro j
  rw [EqGetStack.fin]
  rw [EqGetStack.fin]
  simp [GetElem.getElem]
  conv_lhs =>
    arg 2
    ext k
    arg 1
    erw [GetMul.eq.MulGetS.fin]
  simp [Ξi]
  simp [GetElem.getElem]
  erw [h_Ξᵢ]
  conv_lhs =>
    arg 2
    ext k
    arg 1
    arg 2
    erw [EqGetStack.fin]
  conv_lhs =>
    arg 2
    ext k
    arg 1
    rw [CoeIte.eq.Ite_CoeS]
    erw [Mul_Ite.eq.Ite_MulS]
  conv_lhs =>
    arg 2
    ext k
    arg 1
    arg 2
    simp
    erw [EqMul_1]
  conv_lhs =>
    arg 2
    ext k
    arg 1
    arg 3
    simp
    erw [EqMul_0'0]
  let mulKV (k : Fin n) : Tensor α [] :=
    let a : Tensor α [] := Ai.get k
    let v : Tensor α [] := (V.get k).get j
    a * v
  trans ∑ k : Fin n, if ↑k ∈ Ico (↑i + 1 - l) (↑i + u) then mulKV k else 0
  ·
    apply Fin.Sum.of.All_Eq
    intro k
    let a : Tensor α [] := Ai.get k
    let v : Tensor α [] := (V.get k).get j
    change (if ↑k ∈ Ico (↑i + 1 - l) (↑i + u) then a else 0) * v = if ↑k ∈ Ico (↑i + 1 - l) (↑i + u) then mulKV k else 0
    split_ifs
    ·
      simp only [a, v, mulKV]
    ·
      apply Eq.of.EqDataS
      dsimp [HMul.hMul]
      ext idx
      simp [List.Vector.get_map, EqData0'0]
      fin_cases idx
      change (0 : α) * v.data[0] = 0
      apply EqMul0_0
  ·
    let a0 : ℕ := ↑i + 1 - l
    let b0 : ℕ := ↑i + u
    let Z : Tensor α [n] := [k < n] mulKV k
    have hZ : ∀ k : Fin n, Z.get k = mulKV k := by
      intro k
      simp only [Z]
      erw [EqGetStack.fin]
    trans ∑ k : Fin n, if ↑k ∈ Ico a0 b0 then Z.get k else 0
    ·
      apply Fin.Sum.of.All_Eq
      intro k
      rw [hZ]
    ·
      erw [Sum_IteIn_Ico.eq.SumGetSlice.fin]
      rw [Sum_0.eq.Sum_Get.fin]
      apply Fin.Sum.of.All_Eq
      intro t
      have hk : t < b0 ⊓ n - a0 := LengthSlice.eq.SubMin b0 n a0 ▸ t.isLt
      have hZt := GetGetSlice.eq.Get_Add.of.GtSubMin hk Z
      have hA := GetGetSlice.eq.Get_Add.of.GtSubMin hk Ai
      have hV := GetGetSlice.eq.Get_Add.of.GtSubMin hk V
      simp [GetElem.getElem] at hZt hA hV ⊢
      rw [hZt, hZ]
      dsimp [mulKV]
      erw [hA, hV]
      rfl


-- created on 2026-08-14
-- updated on 2026-08-20
