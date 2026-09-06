import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Lemma.Bool.SEq.is.Eq
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetEye.eq.Delta
import Lemma.Tensor.GetHstack.eq.Get.of.Lt
import Lemma.Tensor.GetHstack.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import sympy.matrices.determinant
import sympy.matrices.expressions.special
open Bool Equiv Matrix Nat Tensor
set_option maxHeartbeats 800000


private abbrev blockSwap (α : Type*) [AddMonoidWithOne α] [CharZero α] (m n : ℕ) : Tensor α [m + n, n + m] :=
  (0 : Tensor α [m, n]).hstack (Tensor.eye m) ++ (Tensor.eye n).hstack (0 : Tensor α [n, m])


@[main]
private lemma main
  [CommRing α] [CharZero α]
  {m n : ℕ} :
-- imply
  ((0 : Tensor α [m, n]).hstack (Tensor.eye m) ++ (Tensor.eye n).hstack (0 : Tensor α [n, m])).det = (-1) ^ (m * n) := by
-- proof
  calc
    _ = (cast (by grind) (blockSwap α m n) : Tensor α [n + m, n + m]).toMatrix.det := by
      unfold Tensor.det
      rw [dif_neg (by grind : ¬[m + n, n + m].length > 2)]
      rw [dif_neg (by grind : ¬[m + n, n + m].length < 2)]
      simp [Nat.add_comm m n]
    _ = (cast (congrArg (fun t => Tensor α [m + n, t]) (Nat.add_comm n m)) (blockSwap α m n)).toMatrix.det := by
      apply Eq.trans
      ·
        have {a b : ℕ} (h : a = b) (X : Tensor α [a, a]) :
            X.toMatrix.det = (cast (by rw [h]) X : Tensor α [b, b]).toMatrix.det := by
          subst h
          rfl
        apply this (Nat.add_comm n m)
      apply congrArg Matrix.det
      apply congrArg Tensor.toMatrix
      apply eq_of_heq
      apply HEq.trans (cast_heq _ _)
      apply HEq.trans (cast_heq _ _)
      apply (cast_heq _ _).symm
    _ = ([i < m + n] [j < m + n]
          (if (i : ℕ) < m then
            if (j : ℕ) < n then (0 : Tensor α [])
            else ↑(KroneckerDelta (i : ℕ) ((j : ℕ) - n))
          else
            if (j : ℕ) < n then ↑(KroneckerDelta ((i : ℕ) - m) (j : ℕ))
            else 0)).toMatrix.det := by
      apply congrArg Matrix.det
      apply congrArg Tensor.toMatrix
      apply Eq.of.All_EqGetS.fin
      intro i
      apply Eq.of.All_EqGetS.fin
      intro j
      have hs : [m + n, n + m] = [m + n, m + n] := by grind
      have delta_fin_nat {N : ℕ} (i j : Fin N) :
          KroneckerDelta i j = KroneckerDelta (i : ℕ) (j : ℕ) := by
        simp [KroneckerDelta, Fin.ext_iff]
      have get_block (i : Fin (m + n)) (j : Fin (n + m)) :
          id (α := Tensor α []) (blockSwap α m n)[(i : ℕ)][(j : ℕ)] =
            if (i : ℕ) < m then
              if (j : ℕ) < n then
                (0 : Tensor α [])
              else
                ↑(KroneckerDelta (i : ℕ) ((j : ℕ) - n))
            else
              if (j : ℕ) < n then
                ↑(KroneckerDelta ((i : ℕ) - m) (j : ℕ))
              else
                0 := by
        if hi : (i : ℕ) < m then
          have hrow :=
            GetAppend.eq.Get.of.Lt (s := [n + m]) hi
              ((0 : Tensor α [m, n]).hstack (Tensor.eye m))
              ((Tensor.eye n).hstack (0 : Tensor α [n, m]))
          if hj : (j : ℕ) < n then
            have hcell :=
              GetHstack.eq.Get.of.Lt hj (0 : Tensor α [m, n]) (Tensor.eye m) ⟨(i : ℕ), hi⟩
            have hz := EqGet0_0.fin (α := α) (s := [m, n]) ⟨(i : ℕ), hi⟩
            have hz' := EqGet0_0.fin (α := α) (s := [n]) ⟨(j : ℕ), hj⟩
            simp [hi, hj]
            simp only [id] at hcell ⊢
            apply Eq.trans (congrArg (fun t : Tensor α [n + m] => id (α := Tensor α []) t[(j : ℕ)]) hrow)
            apply Eq.trans hcell
            simp [GetElem.getElem] at hz hz' ⊢
            rw [hz]
            exact hz'
          else
            have hcell :=
              GetHstack.eq.Get_Sub.of.GtAdd.Ge (le_of_not_gt hj) j.isLt
                (0 : Tensor α [m, n]) (Tensor.eye m) ⟨(i : ℕ), hi⟩
            have he := GetEye.eq.Delta.fin (α := α) (n := m) ⟨(i : ℕ), hi⟩ ⟨(j : ℕ) - n, by grind⟩
            simp [hi, hj]
            simp only [id] at hcell ⊢
            apply Eq.trans (congrArg (fun t : Tensor α [n + m] => id (α := Tensor α []) t[(j : ℕ)]) hrow)
            apply Eq.trans hcell
            simp [GetElem.getElem] at he ⊢
            apply he.trans
            simp [delta_fin_nat]
            rfl
        else
          have hrow :=
            GetAppend.eq.Get_Sub.of.GtAdd.Ge (s := [n + m]) (le_of_not_gt hi) i.isLt
              ((0 : Tensor α [m, n]).hstack (Tensor.eye m))
              ((Tensor.eye n).hstack (0 : Tensor α [n, m]))
          if hj : (j : ℕ) < n then
            have him : (i : ℕ) - m < n := by grind
            have hcell :=
              GetHstack.eq.Get.of.Lt hj (Tensor.eye n) (0 : Tensor α [n, m]) ⟨(i : ℕ) - m, him⟩
            have he := GetEye.eq.Delta.fin (α := α) (n := n) ⟨(i : ℕ) - m, him⟩ ⟨(j : ℕ), hj⟩
            simp [hi, hj]
            simp only [id] at hcell ⊢
            apply Eq.trans (congrArg (fun t : Tensor α [n + m] => id (α := Tensor α []) t[(j : ℕ)]) hrow)
            apply Eq.trans hcell
            simp [GetElem.getElem] at he ⊢
            apply he.trans
            simp [delta_fin_nat]
            rfl
          else
            have him : (i : ℕ) - m < n := by grind
            have hjn : (j : ℕ) - n < m := by grind
            have hcell :=
              GetHstack.eq.Get_Sub.of.GtAdd.Ge (le_of_not_gt hj) j.isLt
                (Tensor.eye n) (0 : Tensor α [n, m]) ⟨(i : ℕ) - m, him⟩
            have hz := EqGet0_0.fin (α := α) (s := [n, m]) ⟨(i : ℕ) - m, him⟩
            have hz' := EqGet0_0.fin (α := α) (s := [m]) ⟨(j : ℕ) - n, hjn⟩
            simp [hi, hj]
            simp only [id] at hcell ⊢
            apply Eq.trans (congrArg (fun t : Tensor α [n + m] => id (α := Tensor α []) t[(j : ℕ)]) hrow)
            apply Eq.trans hcell
            simp [GetElem.getElem] at hz hz' ⊢
            rw [hz]
            exact hz'
      have hR :=
        EqGetStack.fin
          (fun i : Fin (m + n) =>
            [j < m + n]
              (if (i : ℕ) < m then
                if (j : ℕ) < n then (0 : Tensor α [])
                else ↑(KroneckerDelta (i : ℕ) ((j : ℕ) - n))
              else
                if (j : ℕ) < n then ↑(KroneckerDelta ((i : ℕ) - m) (j : ℕ))
                else 0))
          i
      have hR' :=
        EqGetStack.fin
          (fun j : Fin (m + n) =>
            if (i : ℕ) < m then
              if (j : ℕ) < n then (0 : Tensor α [])
              else ↑(KroneckerDelta (i : ℕ) ((j : ℕ) - n))
            else
              if (j : ℕ) < n then ↑(KroneckerDelta ((i : ℕ) - m) (j : ℕ))
              else 0)
          j
      rw [show
          cast (congrArg (fun t => Tensor α [m + n, t]) (Nat.add_comm n m)) (blockSwap α m n) =
            cast (congrArg (Tensor α) hs) (blockSwap α m n)
          by congr 1]
      simp
      apply Eq.trans
        (Eq.of.SEq
          (SEqGetS.of.SEq.GtLength
            (A := (cast (congrArg (Tensor α) hs) (blockSwap α m n))[i])
            (B := (blockSwap α m n)[i]) (i := (j : ℕ))
            (by grind)
            (GetCast.as.Get.of.Eq.GtLength_0.right.fin (s := [m + n, n + m]) (s' := [m + n, m + n])
              (by grind) hs (blockSwap α m n) i)))
      have hb := get_block i ⟨(j : ℕ), by grind⟩
      simp only [id] at hb
      apply Eq.trans hb
      simp at hR hR' ⊢
      erw [hR, hR']
    _ = ((1 : Matrix (Fin (m + n)) (Fin (m + n)) (Tensor α [])).submatrix id ((finRotate (m + n)) ^ m)).det := by
      apply congrArg Matrix.det
      ext i j
      simp [Tensor.toMatrix, Matrix.submatrix, Matrix.one_apply]
      have val_finRotate_pow (j : Fin (m + n)) :
          (((finRotate (m + n)) ^ m) j : ℕ) = if (j : ℕ) < n then m + (j : ℕ) else (j : ℕ) - n := by
        if hN : m + n = 0 then
          grind
        else
          have : NeZero (m + n) := ⟨hN⟩
          have val_finRotate_pow_mod {N k : ℕ} [NeZero N] (i : Fin N) :
              (((finRotate N) ^ k) i : ℕ) = (i.val + k) % N := by
            induction k with
            | zero =>
              simp [Nat.mod_eq_of_lt i.isLt]
            | succ k ih =>
              rw [_root_.pow_succ', Perm.mul_apply, finRotate_apply]
              have h := Fin.val_add ((finRotate N ^ k) i) (1 : Fin N)
              simp at h
              rw [h, ih, Nat.mod_add_mod]
              rfl
          rw [val_finRotate_pow_mod]
          if hj : (j : ℕ) < n then
            rw [if_pos hj, Nat.mod_eq_of_lt (by grind), Nat.add_comm]
          else
            rw [if_neg hj]
            have hdiv : ((j : ℕ) + m) / (m + n) = 1 := Nat.div_eq_of_lt_le (by grind) (by grind)
            rw [Nat.mod_def, hdiv]
            grind
      have hi := EqGetStack.fin
        (fun i : Fin (m + n) =>
          [j < m + n]
            (if (i : ℕ) < m then
              if (j : ℕ) < n then (0 : Tensor α [])
              else ↑(KroneckerDelta (i : ℕ) ((j : ℕ) - n))
            else
              if (j : ℕ) < n then ↑(KroneckerDelta ((i : ℕ) - m) (j : ℕ))
              else 0))
        i
      have hj := EqGetStack.fin
        (fun j : Fin (m + n) =>
          if (i : ℕ) < m then
            if (j : ℕ) < n then (0 : Tensor α [])
            else ↑(KroneckerDelta (i : ℕ) ((j : ℕ) - n))
          else
            if (j : ℕ) < n then ↑(KroneckerDelta ((i : ℕ) - m) (j : ℕ))
            else 0)
        j
      simp [GetElem.getElem] at hi hj ⊢
      erw [hi, hj]
      have hτ := val_finRotate_pow j
      rw [Delta.eq.Ite]
      if hi : (i : ℕ) < m then
        if hj : (j : ℕ) < n then
          have hne : i ≠ ((finRotate (m + n)) ^ m) j := by
            intro h
            simp [Fin.ext_iff, hτ, hj] at h
            grind
          simp [hi, hj, hne]
        else
          have hiff : i = ((finRotate (m + n)) ^ m) j ↔ (i : ℕ) = (j : ℕ) - n := by
            simp [Fin.ext_iff, hτ, hj]
          simp [hi, hj, hiff]
          split_ifs
          ·
            apply Nat.cast_one
          ·
            apply Nat.cast_zero
      else
        if hj : (j : ℕ) < n then
          have hiff : i = ((finRotate (m + n)) ^ m) j ↔ (i : ℕ) = m + (j : ℕ) := by
            simp [Fin.ext_iff, hτ, hj]
          have hΔ : (i : ℕ) - m = (j : ℕ) ↔ (i : ℕ) = m + (j : ℕ) := by
            omega
          simp [hi, hj, hiff, Delta.eq.Ite, hΔ]
          split_ifs
          ·
            apply Nat.cast_one
          ·
            apply Nat.cast_zero
        else
          have hne : i ≠ ((finRotate (m + n)) ^ m) j := by
            intro h
            simp [Fin.ext_iff, hτ, hj] at h
            grind
          simp [hi, hj, hne]
    _ = (-1) ^ (m * n) := by
      rw [det_permute', det_one, mul_one]
      rw [map_pow, sign_finRotate, ← pow_mul]
      rw [show (m + n - 1) * m = m * n + m * (m - 1) by
        cases m with
        | zero =>
          grind
        | succ k =>
          grind]
      have even_mul_pred : Even (m * (m - 1)) := by
        cases m with
        | zero =>
          grind
        | succ k =>
          simpa [mul_comm, Nat.succ_eq_add_one] using Nat.even_mul_succ_self k
      rw [pow_add, Even.neg_one_pow even_mul_pred]
      simp [Int.cast_neg, Int.cast_one]


-- created on 2026-09-06
