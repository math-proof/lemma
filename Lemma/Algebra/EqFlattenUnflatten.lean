import Lemma.Algebra.AppendValS.eq.Val.of.EqAdd
import Lemma.Algebra.Eq.of.EqValS
import Lemma.Algebra.ValAppend.eq.AppendValS
import Lemma.Algebra.Add_Mul.eq.MulAdd_1
import Lemma.Algebra.ValFlattenCons.eq.ValAppend_Flatten
import Lemma.Algebra.Unflatten.eq.Cons_Unflatten.of.SEq_Append
import Lemma.Logic.HEq.of.SEq
import Lemma.Algebra.HEq.of.EqValS
open Algebra Logic


@[main, comm]
private lemma main
-- given
  (v : List.Vector α (m * n)) :
-- imply
  v.unflatten.flatten = v := by
-- proof
  induction m with
  | zero =>
    let ⟨v, h_v⟩ := v
    cases v
    simp only [List.Vector.unflatten, List.Vector.flatten]
    congr
    simp at h_v
  | succ m ih =>
    have h_sum : n + m * n = (m + 1) * n := by
      ring
    have h_append := AppendValS.eq.Val.of.EqAdd h_sum v
    have h_eq : (m + 1) * n - n = m * n := by
      ring_nf
      simp
    let v1 : List.Vector α (m * n) := cast (by rw [h_eq]) (List.Vector.drop n v)
    have h_v1 : (List.Vector.drop n v).val = v1.val := by
      simp [v1]
      congr
      simp [h_eq]
      simp
    rw [h_v1] at h_append
    have h_eq : n ⊓ (m + 1) * n = n := by
      simp
      linarith
    let v0 : List.Vector α n := cast (by rw [h_eq]) (List.Vector.take n v)
    have h_v0 : (List.Vector.take n v).val = v0.val := by
      simp [v0]
      congr
      simp [h_eq]
      simp
    rw [h_v0] at h_append
    have ih := ih v1
    have h_eq : (v0.val ++ v1.val).length = (m + 1) * n := by
      simp
      rw [h_sum]
    let v' : List.Vector α ((m + 1) * n) := ⟨v0.val ++ v1.val, h_eq⟩
    have h_v : v = v' := by
      apply Eq.of.EqValS
      rw [← h_append]
    rw [h_v]
    have h_v_append : v' ≃ v0 ++ v1 := by
      simp [v']
      simp [SEq]
      simp [AppendValS.eq.ValAppend]
      constructor
      .
        ring
      .
        apply HEq.of.EqValS
        simp
    rw [Unflatten.eq.Cons_Unflatten.of.SEq_Append h_v_append]
    have h_unflatten := ValFlattenCons.eq.ValAppend_Flatten v0 v1.unflatten
    rw [ih] at h_unflatten
    apply Eq.of.EqValS
    rw [h_unflatten]
    congr
    ·
      simp [Add_Mul.eq.MulAdd_1]
    ·
      apply HEq.of.SEq h_v_append.symm


-- created on 2025-05-31
