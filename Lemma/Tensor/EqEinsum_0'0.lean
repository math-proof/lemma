import sympy.matrices.expressions.matmul
import torch.Tensor.reshape
import torch.Tensor.bmm
import torch.Tensor.select
import Lemma.Tensor.Cast_ResizeCast_0.eq.Zero
import Lemma.Tensor.EqBmm_0'0
import Lemma.Tensor.EqCast_0'0.of.Eq
import Lemma.Tensor.Select0.eq.Zero
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.List.SetAppend.eq.Append_Set.of.LeLength
open Tensor


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
  {n kk0 : ℕ} {rest : List ℕ}
-- given
  (X : Tensor α [n]) (n' : ℕ) :
-- imply
  Tensor.einsum X (0 : Tensor α (n' :: kk0 :: rest)) =
    (0 : Tensor α (Tensor.matmul_shape [n] (n' :: kk0 :: rest))) := by
-- proof
  unfold Tensor.einsum
  rw [dif_neg (by simp), dif_neg (by simp), dif_pos (by simp)]
  simp (config := { zeta := true }) only []
  rw [dif_neg (by simp)]
  let bs' := (n' :: kk0 :: rest).take ((n' :: kk0 :: rest).length - 2)
  let nn1 := (n' :: kk0 :: rest)[rest.length]
  let nn := n ⊔ nn1
  let kk := (n' :: kk0 :: rest)[(n' :: kk0 :: rest).length - 1]
  let Xr0 : Tensor α [nn] :=
    cast (congrArg (Tensor α) rfl) (X.resize ⟨0, by grind⟩ nn)
  let Xr : Tensor α (bs' ++ [1, nn]) :=
    Xr0.reshape (bs' ++ [1, nn]) (by simp)
  have hs1 : (n' :: kk0 :: rest) = bs' ++ [nn1, kk] :=
    (List.EqAppendTake__ListGet.of.GeLength_2
      (s := n' :: kk0 :: rest) (by simp)).symm
  let d : Fin (bs' ++ [nn1, kk]).length := ⟨bs'.length, by grind⟩
  have hs2 :
      (bs' ++ [nn1, kk]).set d nn = bs' ++ [nn, kk] := by
    rw [List.SetAppend.eq.Append_Set.of.LeLength (Nat.le_refl _)
        [nn1, kk] nn]
    have hsub : (bs'.length - bs'.length) = 0 := by omega
    rw [hsub, List.Set_0.eq.Cons_Tail.of.GtLength_0 (by simp)]
    simp
  let Yt :=
    cast (congrArg (Tensor α) hs2)
      ((cast (congrArg (Tensor α) hs1)
        (0 : Tensor α (n' :: kk0 :: rest))).resize d nn)
  have hY : Yt = 0 :=
    Tensor.Cast_ResizeCast_0.eq.Zero d nn
      (congrArg (Tensor α) hs1) hs1
      (congrArg (Tensor α) hs2) hs2
  have hb : Xr.bmm Yt = 0 :=
    (congrArg (fun Y => Xr.bmm Y) hY).trans (Tensor.EqBmm_0'0 Xr)
  let or : Fin (bs' ++ [1, kk]).length :=
    ⟨(n' :: kk0 :: rest).length - 2, by
      simp [bs', List.length_append]; omega⟩
  let i : Fin ((bs' ++ [1, kk])[or]) := ⟨0, by
    have hlen : bs'.length = (n' :: kk0 :: rest).length - 2 := by
      simp [bs', List.length_take]; omega
    have hle : bs'.length ≤ (↑or : ℕ) := by
      rw [hlen]
    show 0 < (bs' ++ [1, kk])[(↑or : ℕ)]
    rw [List.getElem_append_right hle]
    simp [hlen, or]⟩
  have hp : (bs' ++ [1, kk]).eraseIdx ((n' :: kk0 :: rest).length - 2) =
      Tensor.matmul_shape [n] (n' :: kk0 :: rest) := by
    unfold Tensor.matmul_shape
    rw [dif_neg (by simp), dif_neg (by simp), dif_pos (by simp)]
    simp [bs', kk]
    rw [List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
    simp only [List.EraseIdx.eq.Append_Drop_Add_1]
    have hmin : rest.length ⊓ (rest.length + 2) = rest.length := by
      rw [Nat.min_eq_left (by omega)]
    simp [hmin]
    exact (List.Drop.eq.ListGet.of.GtLength_0 (by simp)).symm
  have hz : cast (congrArg (Tensor α) hp) ((Xr.bmm Yt).select or i) = 0 :=
    (congrArg (fun Z => cast (congrArg (Tensor α) hp) (Z.select or i)) hb).trans
      ((congrArg (fun t => cast (congrArg (Tensor α) hp) t)
          (Tensor.Select0.eq.Zero (o := or) i)).trans
        (Tensor.EqCast_0'0.of.Eq hp))
  convert hz
  · simp
  · simp (config := { zeta := true }) only [Xr0, Xr, bs']; rfl
  · simp


-- created on 2026-09-16
