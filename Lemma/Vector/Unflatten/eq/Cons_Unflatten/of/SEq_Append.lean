import Lemma.Nat.AddMul.lt.Mul
import Lemma.Nat.Add_Mul.eq.MulAdd_1
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.eq.MulAdd_1
import Lemma.Nat.AddAdd
import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.Lt.of.AddMul.lt.Mul
import Lemma.Vector.Val.of.SEq
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.Get.of.SEq_Append.Lt.Lt
import Lemma.Vector.Get_Add.eq.Get.of.SEq_Append.Lt.LtAdd
open Vector Nat


@[main]
private lemma main
  {v : List.Vector α ((m + 1) * n)}
  {head : List.Vector α n}
  {tail : List.Vector α (m * n)}
-- given
  (h : v ≃ head ++ tail) :
-- imply
  v.unflatten = head ::ᵥ tail.unflatten := by
-- proof
  ext i j
  have hij := AddMul.lt.Mul i j
  have h_v := Get_AddMul.eq.GetUnflatten v
  simp [GetElem.getElem] at h_v
  rw [← h_v]
  simp [List.Vector.get]
  let i' : ℕ := i
  have h_eq_i : i' = i := by
    rfl
  simp [← h_eq_i]
  match hi : i' with
  | 0 =>
    simp
    have hj : j < (m + 1) * n := by
      nlinarith
    have hj' := j.isLt
    have := Get.of.SEq_Append.Lt.Lt hj hj' h
    aesop
  | i + 1 =>
    simp [MulAdd_1.eq.Add_Mul]
    simp [AddAdd.eq.Add_Add]
    simp [← h_eq_i] at hij
    rw [MulAdd_1.eq.AddMul, MulAdd_1.eq.AddMul] at hij
    rw [AddAdd.comm] at hij
    have hij := Lt.of.LtAddS hij
    have h_eq := Get_Add.eq.Get.of.SEq_Append.Lt.LtAdd (show n + (i * n + j) < (m + 1) * n by linarith) hij h
    erw [GetUnflatten.eq.Get_AddMul tail ⟨i, by grind⟩]
    aesop


-- created on 2025-05-31
-- updated on 2026-08-24
