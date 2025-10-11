import sympy.tensor.Basic
import Lemma.Tensor.HEq.of.SEqDataS.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.Lt_Length
import Lemma.Nat.Any_Eq_AddMul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
open Tensor Bool Vector List Nat


@[main]
private lemma main
  {X : Tensor α s}
  {X' : Tensor α s'}
  {n n' : ℕ}
  {d : Fin s.length}
  {d' : Fin s'.length}
-- given
  (h_s : s = s')
  (h_n : n = n')
  (h_d : d.val = d'.val)
  (h : X ≃ X') :
-- imply
  X.repeat n d ≃ X'.repeat n' d' := by
-- proof
  simp [SEq] at *
  constructor
  ·
    aesop
  ·
    unfold Tensor.repeat
    simp
    apply HEq.of.SEqDataS.Eq
    ·
      aesop
    ·
      apply SEqCastS.of.SEq.Eq.Eq
      repeat apply MulProd_Mul_Prod.eq.ProdSet__Mul_Get.of.Lt_Length
      apply SEq.of.All_EqGetS.Eq (by aesop)
      intro t
      let ⟨i, j, h_t⟩ := Any_Eq_AddMul t
      simp [GetFlatten.eq.Get.of.Eq_AddMul h_t]
      let i' : Fin (s'.take d').prod := ⟨i, by simp [← h_d, ← h_s]⟩
      let j' : Fin (n' * (s'.drop d').prod) := ⟨j, by simp [← h_d, ← h_s, ← h_n]⟩
      have h_i : i.val = i'.val := by rfl
      have h_j : j.val = j'.val := by rfl
      simp [h_s, h_n, h_d, h_i, h_j] at h_t
      rw [GetFlatten.eq.Get.of.Eq_AddMul h_t]
      rw [GetRepeat.eq.Get_Mod (X.data.splitAt d)[i.val]]
      simp [GetRepeat.eq.Get_Mod (X'.data.splitAt d')[i'.val]]
      repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop]
      simp [i', j', ← h_d, ← h_s]
      congr <;>
      .
        aesop


-- created on 2025-10-11
