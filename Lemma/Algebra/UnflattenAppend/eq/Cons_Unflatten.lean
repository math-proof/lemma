import stdlib.List.Vector
import Lemma.Algebra.Get_AddMul.eq.GetUnflatten
import Lemma.Algebra.AddMul.lt.Mul
import Lemma.Algebra.MulAdd_1.eq.Add_Mul
import Lemma.Algebra.EqGetS.of.Val.eq.ValAppend
import Lemma.Algebra.AddAdd.eq.Add_Add
import Lemma.Algebra.Get_Add.eq.Get.of.Val.eq.ValAppend
import Lemma.Algebra.MulAdd_1.eq.AddMul
import Lemma.Algebra.AddAdd.comm
import Lemma.Algebra.Lt.of.LtAddS
import Lemma.Algebra.Lt.of.AddMul.lt.Mul
open Algebra


@[main]
private lemma main
  [Inhabited α]
-- given
  (head : List.Vector α n)
  (tail : List.Vector α (m * n)) :
-- imply
  let v_append : List.Vector α (m.succ * n) := cast (by rw [Nat.succ_mul, add_comm]) (head ++ tail)
  v_append.unflatten = head ::ᵥ tail.unflatten := by
-- proof
  intro v_append
  ext i j
  have h_v_append := Get_AddMul.eq.GetUnflatten v_append i j
  simp [GetElem.getElem] at h_v_append
  have hij := AddMul.lt.Mul i j
  simp [hij] at h_v_append
  rw [← h_v_append]
  simp [List.Vector.get]
  let i' : ℕ := i
  have h_eq_i : i' = i := by
    rfl
  have h_eq : v_append.val = (head ++ tail).val := by
    congr
    simp [MulAdd_1.eq.Add_Mul]
    simp [v_append]
  simp [← h_eq_i]
  match hi : i' with
  | .zero =>
    simp
    have h_eq := EqGetS.of.Val.eq.ValAppend h_eq j
    simp [GetElem.getElem] at h_eq
    have hj : j < (m + 1) * n := by
      nlinarith
    simp [hj] at h_eq
    simp [List.Vector.get] at h_eq
    assumption
  | .succ i =>
    simp
    simp [MulAdd_1.eq.Add_Mul]
    simp [AddAdd.eq.Add_Add]
    let hij' := hij
    simp [← h_eq_i] at hij
    rw [MulAdd_1.eq.AddMul, MulAdd_1.eq.AddMul] at hij
    rw [AddAdd.comm] at hij
    have hij := Lt.of.LtAddS hij
    have h_eq := Get_Add.eq.Get.of.Val.eq.ValAppend h_eq (⟨i * n + j, hij⟩ : Fin (m * n))
    have hi := Lt.of.AddMul.lt.Mul hij
    have h_v_tail := Get_AddMul.eq.GetUnflatten tail (⟨i, hi⟩ : Fin m) j
    simp [GetElem.getElem] at h_v_tail
    simp [hij, hi, List.Vector.get] at h_v_tail
    rw [← h_v_tail]
    simp [GetElem.getElem] at h_eq
    simp [← h_eq_i] at hij'
    rw [MulAdd_1.eq.Add_Mul, AddAdd.eq.Add_Add] at hij'
    simp [hij', hij, List.Vector.get] at h_eq
    assumption


-- created on 2025-05-10
