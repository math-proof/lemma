import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.List.EqRotateRotate.of.Le_Length
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Nat.LtVal
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.List.ProdRotate.eq.Prod
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.List.EqAppendTake__Drop
import Lemma.Nat.Sub_Mod.eq.ModSub
import Lemma.List.TakeRotate.eq.Drop
import Lemma.Nat.EqMod.of.Lt
import Lemma.List.DropRotate.eq.Take
import Lemma.Tensor.SEqRotate_Length
import Lemma.List.LengthRotate.eq.Length
import Lemma.Tensor.SEqRotate_0
import Lemma.Nat.Sub.eq.Zero
open Vector Tensor List Bool Nat


@[main]
private lemma main
-- given
  (h : i ≤ s.length)
  (X : Tensor α s) :
-- imply
  (X.rotate i).rotate (s.length - i) ≃ X := by
-- proof
  by_cases h_i : i = s.length ∨ i = 0
  ·
    obtain h_i | h_i := h_i <;>
      subst h_i
    ·
      have := SEqRotate_0 (X.rotate s.length)
      rw [← Sub.eq.Zero s.length] at this
      apply SEq.trans this
      apply SEqRotate_Length
    ·
      have := SEqRotate_Length (X.rotate 0)
      rw [← LengthRotate.eq.Length s 0]
      apply SEq.trans this
      apply SEqRotate_0
  ·
    unfold Tensor.rotate
    apply SEq.of.SEqDataS.Eq
    ·
      rw [EqRotateRotate.of.Le_Length h]
    ·
      simp
      apply SEqCast.of.SEq.Eq.Eq
      ·
        rw [MulProdS.eq.ProdAppend]
        rw [AppendDrop__Take.eq.Rotate]
      ·
        rw [EqRotateRotate.of.Le_Length h]
      ·
        apply SEq.of.All_EqGetS.Eq
        ·
          intro t
          have h_t := LtVal t
          let ⟨k, j, h_kj⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
          simp [GetFlatten.eq.Get.of.Eq_AddMul h_kj]
          rw [GetTranspose.eq.Get]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop]
          simp at h_kj ⊢
          rw [GetCast.eq.Get.of.Eq.Lt]
          ·
            simp at h_i
            have : NeZero i := ⟨by omega⟩
            have h_i : i < s.length := by omega
            have := Sub_Mod.eq.ModSub (m := s.length) (n := i) h_i
            let n := (List.take (i % s.length) s).prod
            let m := (List.drop (i % s.length) s).prod
            have h_j := LtVal j
            simp at h_j
            have h_take := TakeRotate.eq.Drop s i
            have h_mod := EqMod.of.Lt h_i
            rw [h_mod] at h_take
            rw [h_take] at h_j
            have h_k := LtVal k
            simp at h_k
            have h_drop := DropRotate.eq.Take s i
            rw [h_mod] at h_drop
            rw [h_drop] at h_k
            rw [GetFlatten.eq.Get.of.Eq_AddMul (i := ⟨j, by simp [h_mod, h_j]⟩) (j := ⟨k, by simpa [h_mod]⟩)]
            ·
              rw [GetTranspose.eq.Get]
              rw [GetSplitAt.eq.Get_AddMul_ProdDrop]
              simp at ⊢ h_kj
              rw [h_take] at h_kj
              simp [h_kj]
              simp [h_mod]
            ·
              simp
              left
              rw [h_drop]
              rw [h_mod]
          ·
            rw [MulProdS.eq.ProdAppend]
            rw [AppendDrop__Take.eq.Rotate]
            rw [ProdRotate.eq.Prod]
            simp only [MulProdS.eq.ProdAppend] at h_t
            rw [AppendDrop__Take.eq.Rotate] at h_t
            rw [EqRotateRotate.of.Le_Length h] at h_t
            have h_k := LtVal k
            have h_j := LtVal j
            have h_lt := AddMul.lt.Mul.of.Lt.Lt h_j h_k
            simp only [MulProdS.eq.ProdAppend] at h_lt
            rw [EqAppendTake__Drop] at h_lt
            simp [ProdRotate.eq.Prod] at h_lt
            assumption
          ·
            rw [MulProdS.eq.ProdAppend]
            rw [AppendDrop__Take.eq.Rotate]
        ·
          rw [MulProdS.eq.ProdAppend]
          rw [AppendDrop__Take.eq.Rotate]
          rw [EqRotateRotate.of.Le_Length h]


-- created on 2025-10-18
-- updated on 2025-10-19
