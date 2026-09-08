import Lemma.Nat.EqCast_0'0
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.GetEye.eq.Delta
import Lemma.Tensor.GetHstack.eq.Get.of.Lt
import Lemma.Tensor.GetHstack.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetSwapMatrix.eq.Ite
open Nat Tensor
set_option maxHeartbeats 800000


private lemma get_tl
  [AddMonoidWithOne α] [CharZero α]
  (i j h k : Fin n) :
  ((SwapMatrix n i j).hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (Tensor.eye 1))[Fin.castAdd 1 h][Fin.castAdd 1 k] = (SwapMatrix n i j)[h][k] := by
  have hrow := GetAppend.eq.Get.of.Lt (s := [n + 1]) h.isLt
    ((SwapMatrix n i j).hstack (0 : Tensor α [n, 1]))
    ((0 : Tensor α [1, n]).hstack (Tensor.eye 1))
  have hcell := GetHstack.eq.Get.of.Lt k.isLt (SwapMatrix n i j) (0 : Tensor α [n, 1]) h
  have hj := Nat.lt_add_right 1 k.isLt
  simp at hcell ⊢
  have hget := congrArg (fun t : Tensor α [n + 1] => (t[k]'hj)) hrow
  simpa [GetElem.getElem] using hget.trans hcell


private lemma get_tr
  [AddMonoidWithOne α] [CharZero α]
  (i j h : Fin n) :
  ((SwapMatrix n i j).hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (Tensor.eye 1))[Fin.castAdd 1 h][Fin.natAdd n (0 : Fin 1)] = 0 := by
  have hrow := GetAppend.eq.Get.of.Lt (s := [n + 1]) h.isLt
    ((SwapMatrix n i j).hstack (0 : Tensor α [n, 1]))
    ((0 : Tensor α [1, n]).hstack (Tensor.eye 1))
  have hj := (Fin.natAdd n (0 : Fin 1)).isLt
  have hcell := GetHstack.eq.Get_Sub.of.GtAdd.Ge (Nat.le_add_right n 0) hj (SwapMatrix n i j) (0 : Tensor α [n, 1]) h
  have hget := congrArg (fun t : Tensor α [n + 1] => (t[(Fin.natAdd n (0 : Fin 1) : ℕ)]'hj)) hrow
  apply Eq.trans hget
  apply Eq.trans hcell
  simp [GetElem.getElem]
  rw [EqGet0_0.fin (s := [n, 1]) ⟨h, h.isLt⟩]
  apply EqGet0_0.fin (s := [1]) ⟨0, by grind⟩


private lemma get_bl
  [AddMonoidWithOne α] [CharZero α]
  (i j k : Fin n) :
  ((SwapMatrix n i j).hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (Tensor.eye 1))[Fin.natAdd n (0 : Fin 1)][Fin.castAdd 1 k] = 0 := by
  have hrow := GetAppend.eq.Get_Sub.of.GtAdd.Ge (s := [n + 1]) (Nat.le_add_right n 0)
    (Fin.natAdd n (0 : Fin 1)).isLt
    ((SwapMatrix n i j).hstack (0 : Tensor α [n, 1]))
    ((0 : Tensor α [1, n]).hstack (Tensor.eye 1))
  have hcell := GetHstack.eq.Get.of.Lt k.isLt (0 : Tensor α [1, n]) (Tensor.eye 1) ⟨0, by grind⟩
  have hget := congrArg (fun t : Tensor α [n + 1] => t[k]'(by grind)) hrow
  simp only [Nat.add_sub_cancel_left] at hget
  apply Eq.trans hget
  apply Eq.trans hcell
  simp [GetElem.getElem]
  rw [EqGet0_0.fin (s := [1, n]) ⟨0, by grind⟩]
  apply EqGet0_0.fin (s := [n]) ⟨k, k.isLt⟩


private lemma get_br
  [AddMonoidWithOne α] [CharZero α]
  (i j : Fin n) :
  ((SwapMatrix n i j).hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (Tensor.eye 1))[Fin.natAdd n (0 : Fin 1)][Fin.natAdd n (0 : Fin 1)] = (Tensor.eye 1)[(0 : Fin 1)][(0 : Fin 1)] := by
  have hj := (Fin.natAdd n (0 : Fin 1)).isLt
  have hrow := GetAppend.eq.Get_Sub.of.GtAdd.Ge (s := [n + 1]) (Nat.le_add_right n 0)
    hj
    ((SwapMatrix n i j).hstack (0 : Tensor α [n, 1]))
    ((0 : Tensor α [1, n]).hstack (Tensor.eye 1))
  have hcell := GetHstack.eq.Get_Sub.of.GtAdd.Ge (Nat.le_add_right n 0) hj (0 : Tensor α [1, n]) (Tensor.eye 1) (0 : Fin 1)
  have hget := congrArg (fun t : Tensor α [n + 1] => (t[(Fin.natAdd n (0 : Fin 1) : ℕ)]'hj)) hrow
  simp only [Nat.add_sub_cancel_left] at hget
  simpa [GetElem.getElem, Fin.val_natAdd, Nat.add_sub_cancel_left] using hget.trans hcell


private lemma swap_tl
  [AddMonoidWithOne α] [CharZero α]
  (i j h k : Fin n) :
  (SwapMatrix (α := α) n i j)[h][k] = (SwapMatrix (n + 1) i j)[Fin.castAdd 1 h][Fin.castAdd 1 k] := by
  erw [GetSwapMatrix.eq.Ite i j h k, GetSwapMatrix.eq.Ite i j (Fin.castAdd 1 h) (Fin.castAdd 1 k)]
  simp [KroneckerDelta, Fin.ext_iff]


private lemma swap_tr
  [AddMonoidWithOne α] [CharZero α]
  (i j h : Fin n) :
  (SwapMatrix (n + 1) i j)[Fin.castAdd 1 h][Fin.natAdd n (0 : Fin 1)] = (0 : Tensor α []) := by
  erw [GetSwapMatrix.eq.Ite i j (Fin.castAdd 1 h) (Fin.natAdd n (0 : Fin 1))]
  simp [KroneckerDelta, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
  have hi := Nat.ne_of_lt i.isLt
  have hj := Nat.ne_of_lt j.isLt
  have hh := Nat.ne_of_lt h.isLt
  split_ifs <;>
  ·
    simp [hi.symm, hj.symm, hh.symm]
    exact EqCast_0'0


private lemma swap_bl
  [AddMonoidWithOne α] [CharZero α]
  (i j k : Fin n) :
  (SwapMatrix (n + 1) i j)[Fin.natAdd n (0 : Fin 1)][Fin.castAdd 1 k] = (0 : Tensor α []) := by
  erw [GetSwapMatrix.eq.Ite i j (Fin.natAdd n (0 : Fin 1)) (Fin.castAdd 1 k)]
  simp [KroneckerDelta, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
  have hi := Nat.ne_of_lt i.isLt
  have hj := Nat.ne_of_lt j.isLt
  have hk := Nat.ne_of_lt k.isLt
  split_ifs with h1 h2
  ·
    grind
  ·
    grind
  ·
    simp [hk]
    exact EqCast_0'0


private lemma swap_br
  [AddMonoidWithOne α] [CharZero α]
  (i j : Fin n) :
  (SwapMatrix (n + 1) i j)[Fin.natAdd n (0 : Fin 1)][Fin.natAdd n (0 : Fin 1)] = (KroneckerDelta (0 : Fin 1) (0 : Fin 1) : Tensor α []) := by
  erw [GetSwapMatrix.eq.Ite i j (Fin.natAdd n (0 : Fin 1)) (Fin.natAdd n (0 : Fin 1))]
  simp [KroneckerDelta, Fin.val_natAdd]
  have hi := Nat.ne_of_lt i.isLt
  have hj := Nat.ne_of_lt j.isLt
  grind


@[main]
private lemma main
  [AddMonoidWithOne α] [CharZero α]
-- given
  (i j : Fin n) :
-- imply
  (SwapMatrix n i j).hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (Tensor.eye 1) = SwapMatrix (n + 1) i j := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro h
  apply Eq.of.All_EqGetS.fin
  intro k
  if hh : h < n then
    have heqh : h = Fin.castAdd 1 ⟨h, hh⟩ := Fin.ext rfl
    if hk : k < n then
      have heqk : k = Fin.castAdd 1 ⟨k, hk⟩ := Fin.ext rfl
      rw [heqh, heqk]
      change ((SwapMatrix n i j).hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (Tensor.eye 1))[Fin.castAdd 1 ⟨h, hh⟩][Fin.castAdd 1 ⟨k, hk⟩] = (SwapMatrix (n + 1) i j)[Fin.castAdd 1 ⟨h, hh⟩][Fin.castAdd 1 ⟨k, hk⟩]
      apply (get_tl i j ⟨h, hh⟩ ⟨k, hk⟩).trans (swap_tl i j ⟨h, hh⟩ ⟨k, hk⟩)
    else
      have hk' : k = n := by omega
      have heqk : k = Fin.natAdd n (0 : Fin 1) := Fin.ext (by simp [Fin.val_natAdd, hk'])
      rw [heqh, heqk]
      change ((SwapMatrix n i j).hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (Tensor.eye 1))[Fin.castAdd 1 ⟨h, hh⟩][Fin.natAdd n (0 : Fin 1)] = (SwapMatrix (n + 1) i j)[Fin.castAdd 1 ⟨h, hh⟩][Fin.natAdd n (0 : Fin 1)]
      apply (get_tr i j ⟨h, hh⟩).trans (swap_tr i j ⟨h, hh⟩).symm
  else
    have hh' : h = n := by omega
    have heqh : h = Fin.natAdd n (0 : Fin 1) := Fin.ext (by simp [Fin.val_natAdd, hh'])
    if hk : k < n then
      have heqk : k = Fin.castAdd 1 ⟨k, hk⟩ := Fin.ext rfl
      rw [heqh, heqk]
      change ((SwapMatrix n i j).hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (Tensor.eye 1))[Fin.natAdd n (0 : Fin 1)][Fin.castAdd 1 ⟨k, hk⟩] = (SwapMatrix (n + 1) i j)[Fin.natAdd n (0 : Fin 1)][Fin.castAdd 1 ⟨k, hk⟩]
      apply (get_bl i j ⟨k, hk⟩).trans (swap_bl i j ⟨k, hk⟩).symm
    else
      have hk' : k = n := by omega
      have heqk : k = Fin.natAdd n (0 : Fin 1) := Fin.ext (by simp [Fin.val_natAdd, hk'])
      rw [heqh, heqk]
      change ((SwapMatrix n i j).hstack (0 : Tensor α [n, 1]) ++ (0 : Tensor α [1, n]).hstack (Tensor.eye 1))[Fin.natAdd n (0 : Fin 1)][Fin.natAdd n (0 : Fin 1)] = (SwapMatrix (n + 1) i j)[Fin.natAdd n (0 : Fin 1)][Fin.natAdd n (0 : Fin 1)]
      apply (get_br i j).trans
      apply (GetEye.eq.Delta (n := 1) (0 : Fin 1) (0 : Fin 1)).trans
      apply (swap_br i j).symm


-- created on 2020-08-30
-- updated on 2026-09-08
