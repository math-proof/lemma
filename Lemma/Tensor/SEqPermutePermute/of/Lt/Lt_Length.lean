import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.List.TakePermute.eq.Take
import Lemma.Nat.EqSub_Sub.of.Gt
import Lemma.Nat.EqMinSub
import Lemma.List.RotateDropPermute.eq.Drop
import Lemma.Int.Add.eq.Sub_Neg
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Int.EqToNat
import Lemma.Nat.SubSub
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqSubAdd
import Lemma.Nat.Sub_Add.eq.SubSub
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.DropPermute.eq.Drop.of.Add.lt.Length
import Lemma.Nat.Add
import Lemma.List.ProdDrop.eq.MulProdS
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.List.RotateDropTakePermute.eq.TakeDrop.of.Add.lt.Length
import Lemma.Tensor.PermuteTailCast.eq.Cast_PermuteTail.of.Eq
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.List.Permute.eq.Rotate.of.GtLength_0
import Lemma.List.EqRotateRotate.of.Le_Length
import Lemma.Tensor.PermuteTail.as.Rotate.of.Eq_Length
import Lemma.Tensor.SEqRotate.of.SEq_Rotate.Le_Length
import Lemma.Tensor.PermuteHead.as.Rotate
import Lemma.Tensor.SEqRotateS.of.Eq.SEq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Nat.LtVal
import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.List.Drop.eq.AppendTakeDrop
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Nat.SubAdd.eq.AddSub.of.Le
import Lemma.Nat.EqMod.of.Lt
import Lemma.List.RotateTakeDrop.eq.DropTakePermute.of.Add.lt.Length
import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.List.RotateRotate.eq.Rotate_Add
import Lemma.List.EqRotate.of.Eq_Length
import Lemma.List.ProdRotate.eq.Prod
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.List.ProdPermute.eq.Prod
import Lemma.Nat.ToNatSub_Neg.eq.Add
open List Tensor Bool Nat Int Vector
set_option maxHeartbeats 4000000


@[main]
private lemma main'
  {s : List ℕ}
-- given
  (h_j : j < s.length)
  (h : i < j)
  (X : Tensor α s) :
-- imply
  let d := j - i
  (X.permute ⟨i, by linarith⟩ d).permute ⟨j, by simpa [LengthPermute.eq.Length]⟩ (-d) ≃ X := by
-- proof
  intro d
  by_cases h_d : d = 0
  .
    simp [d] at h_d
    grind
  .
    simp at h_d
    -- have h_d := Gt_0.of.Ne_0 h_d
    rw [Permute.eq.Ite (d := ⟨j, by simpa [LengthPermute.eq.Length]⟩) (k := -d)]
    have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
    split_ifs with h_sub h_pos h_j_0 h_j_length
    repeat omega
    simp [LengthPermute.eq.Length] at h_j_length
    subst h_j_length
    simp
    apply SEqCast.of.SEq.Eq.Eq
    ·
      rw [EqPermutePermute.of.In_Ioo_Length ⟨h, h_j⟩]
      simp [LengthPermute.eq.Length]
      rw [(show (1 + d : ℤ).toNat = s.length - i by omega)]
      rw [EqSub_Sub.of.Gt (by linarith)]
      rw [EqMinSub]
      rw [(show (d : ℤ) = (s.length - i - 1 : ℕ) by omega)]
      rw [TakePermute.eq.Take ⟨i, by linarith⟩ (s.length - i - 1)]
      simp [RotateDropPermute.eq.Drop (i := ⟨i, by linarith⟩)]
    ·
      rw [EqPermutePermute.of.In_Ioo_Length ⟨by omega, by omega⟩]
    ·
      simp at h_sub
      simp at h_j_length
      rw [h_toNat]
      rw [Permute.eq.Ite (d := ⟨i, by linarith⟩) (k := d)]
      simp
      split_ifs with h_pos? h_i_0 h_i_length
      ·
        subst d h_i_0
        simp
        rw [EqAdd_Sub.of.Ge (by linarith)]
        rw [PermuteTailCast.eq.Cast_PermuteTail.of.Eq]
        ·
          apply SEqCast.of.SEq.Eq.Eq
          ·
            rw [EqAddSub.of.Ge (by linarith)]
            simp [Permute.eq.Rotate.of.GtLength_0]
          ·
            simp [Permute.eq.Rotate.of.GtLength_0]
            rw [EqRotateRotate.of.Le_Length]
            linarith
          ·
            rw [EqAddSub.of.Ge (by linarith)]
            have := PermuteTail.as.Rotate.of.Eq_Length (n := s.length) (by simp) (X.permuteHead s.length)
            apply SEq.trans this
            apply SEqRotate.of.SEq_Rotate.Le_Length
            ·
              simp
            ·
              have := PermuteHead.as.Rotate X
              apply SEq.trans this
              apply SEqRotateS.of.Eq.SEq (by rfl)
              simp
              omega
        ·
          rw [EqAddSub.of.Ge (by linarith)]
          simp
          apply Rotate.eq.Permute.of.GtLength_0
      ·
        sorry
      ·
        omega
      ·
        omega
    ·
      simp
      apply SEq.of.SEqDataS.Eq
      ·
        rw [EqPermutePermute.of.In_Ioo_Length ⟨by omega, by omega⟩]
      ·
        simp
        have h_j : j = d + i := by omega
        have h_rotate := RotateDropTakePermute.eq.TakeDrop.of.Add.lt.Length (s := s) (i := ⟨i, by linarith⟩) (d := d) (by grind)
        simp at h_rotate
        have h_permute := DropPermute.eq.Drop.of.Add.lt.Length (s := s) (i := ⟨i, by grind⟩) (d := d) (by grind)
        simp at h_permute
        rw [Add.comm (a := i)] at h_permute
        apply SEqCast.of.SEq.Eq
        ·
          simp at h_sub
          simp at h_j_length
          rw [h_toNat]
          rw [EqPermutePermute.of.In_Ioo_Length ⟨by omega, by omega⟩]
          simp [LengthPermute.eq.Length]
          repeat rw [EqMin.of.Le (by omega)]
          rw [EqSubAdd.left]
          rw [@Nat.Sub_Add.eq.SubSub]
          rw [EqSubAdd]
          simp [h_j]
          rw [TakeTake.eq.Take.of.Ge (by omega)]
          rw [TakePermute.eq.Take ⟨i, by linarith⟩]
          rw [h_permute]
          have h_drop := ProdDrop.eq.MulProdS s i (d + 1)
          rw [Add_Add.eq.AddAdd] at h_drop
          simp [Add.comm (a := i)] at h_drop
          rw [h_rotate]
          rw [MulMul.eq.Mul_Mul]
          simp [← h_drop]
        ·
          rw [h_toNat]
          apply SEq.of.All_EqGetS.Eq
          ·
            intro t
            have h_t := LtVal t
            let ⟨k, l, h_kl⟩ := Any_EqAddMul.of.Lt_Mul h_t
            simp [GetFlatten.eq.Get.of.Eq_AddMul h_kl.symm]
            unfold Tensor.permuteTail
            simp
            rw [GetCast.eq.Get.of.Eq.Lt]
            ·
              have h_k := LtVal k
              simp only [ProdAppend.eq.MulProdS] at h_k
              let ⟨i', j', h_ij'⟩ := Any_EqAddMul.of.Lt_Mul h_k
              simp [GetFlatten.eq.Get.of.Eq_AddMul h_ij'.symm]
              unfold Tensor.rotate
              simp
              simp only [GetElem.getElem]
              have h_j' := LtVal j'
              rw [GetCast.eq.Get.of.Eq.Lt.fin]
              ·
                simp
                let J := (min (1 + d) ((s.permute ⟨i, by grind⟩ d).take (j + 1)).length - 1) % (((s.permute ⟨i, by grind⟩ d).take (j + 1)).drop (((s.permute ⟨i, by grind⟩ d).take (j + 1)).length - (1 + d))).length
                let S := ((s.permute ⟨i, by grind⟩ d).take (j + 1)).drop (((s.permute ⟨i, by grind⟩ d).take (j + 1)).length - (1 + d))
                let N := (S.take J).prod
                let M := (S.drop J).prod
                simp at h_j'
                rw [LengthPermute.eq.Length] at h_j'
                simp [ProdRotate.eq.Prod] at h_j'
                have h_j' : j' < N * M := by
                  simp [M, N, S]
                  rw [MulProdS.eq.ProdAppend]
                  simp
                  rwa [LengthPermute.eq.Length]
                have h_j' : j' < M * N := by
                  grind
                simp only [M, N] at h_j'
                let ⟨ji, jj, h_iijj⟩ := Any_EqAddMul.of.Lt_Mul h_j'
                simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_iijj.symm]
                rw [GetTranspose.eq.Get.fin]
                repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                rw [Permute.eq.Ite (d := ⟨i, by linarith⟩) (k := d)]
                simp
                split_ifs with h_pos? h_i_0 h_i_length
                ·
                  sorry
                ·
                  sorry
                ·
                  sorry
                ·
                  simp
                  rw [GetCast.eq.Get.of.Eq.Lt.fin]
                  ·
                    sorry
                  ·
                    rw [LengthPermute.eq.Length]
                    rw [EqMin.of.Le (by omega)]
                    simp [h_j, @Nat.Sub_Add.eq.SubSub]
                    rw [SubAdd.eq.AddSub.of.Le (by omega)]
                    simp [EqMin.of.Le (by omega)]
                    sorry
                  ·
                    simp [MulProdS.eq.ProdAppend]
                    rw [ProdPermute.eq.Prod]
              ·
                rw [MulProdS.eq.ProdAppend]
                convert h_j'
                simp
                rw [LengthPermute.eq.Length]
                rw [EqMin.of.Le (by omega)]
                simp [h_j, @Nat.Sub_Add.eq.SubSub]
                rw [SubAdd.eq.AddSub.of.Le (by omega)]
                rw [EqSubAdd]
                rw [EqMin.of.Le (by omega)]
                rw [EqSubAdd.left]
                rw [EqMod.of.Lt (by omega)]
                rw [h_rotate]
                have := RotateTakeDrop.eq.DropTakePermute.of.Add.lt.Length (s := s) (i := ⟨i, by omega⟩) (d := d) (by grind)
                rw [← this]
                simp at this
                have := congrArg (·.drop d) this
                simp at this
                simp [← this]
                rw [← Rotate.eq.AppendDrop__Take.of.Le_Length (by simp; omega)]
                rw [RotateRotate.eq.Rotate_Add]
                apply EqRotate.of.Eq_Length
                simp
                rw [EqMin.of.Le (by omega)]
                apply Add.comm
              ·
                rw [MulProdS.eq.ProdAppend]
                apply congrArg
                simp
                rw [LengthPermute.eq.Length]
                rw [EqMin.of.Le (by omega)]
                simp [h_j, @Nat.Sub_Add.eq.SubSub]
                rw [SubAdd.eq.AddSub.of.Le (by omega)]
                rw [EqSubAdd]
                rw [EqMin.of.Le (by omega)]
                rw [EqSubAdd.left]
                rw [EqMod.of.Lt (by omega)]
                rw [h_rotate]
                have := RotateTakeDrop.eq.DropTakePermute.of.Add.lt.Length (s := s) (i := ⟨i, by omega⟩) (d := d) (by grind)
                rw [← this]
                simp at this
                have := congrArg (·.drop d) this
                simp at this
                simp [← this]
                rw [← Rotate.eq.AppendDrop__Take.of.Le_Length (by simp; omega)]
                rw [RotateRotate.eq.Rotate_Add]
                apply EqRotate.of.Eq_Length
                simp
                rw [EqMin.of.Le (by omega)]
                apply Add.comm
            ·
              rw [MulProdS.eq.ProdAppend]
              apply LtVal
            ·
              rw [MulProdS.eq.ProdAppend]
          ·
            simp
            rw [LengthPermute.eq.Length]
            rw [EqMin.of.Le (by omega)]
            simp [h_j, @Nat.Sub_Add.eq.SubSub]
            rw [EqMin.of.Le (by omega)]
            rw [EqSubAdd.left]
            repeat rw [MulProdS.eq.ProdAppend]
            apply congrArg
            rw [h_permute]
            rw [TakeTake.eq.Take.of.Ge (by omega)]
            have := TakePermute.eq.Take (s := s) ⟨i, by grind⟩ d
            simp at this
            rw [this]
            simp [h_rotate]
            have := Drop.eq.AppendTakeDrop s i (d + 1)
            rw [Add_Add.eq.AddAdd] at this
            rw [Add.comm (a := i)] at this
            simp [← this]


-- created on 2025-10-12
-- updated on 2025-10-19
