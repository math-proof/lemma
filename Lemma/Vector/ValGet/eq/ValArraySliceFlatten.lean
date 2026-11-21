import Def.Data.Vector.Basic
import Lemma.Vector.EqCons_Tail
import Lemma.List.DropDrop.eq.Drop_Add
import Theorem.Bool.UFn.of.Eq
open Vector List Bool


@[path]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m) :
-- imply
  v[i].val = (v.flatten.array_slice (i * n) n).val := by
-- proof
  simp [List.Vector.array_slice]
  simp [List.Vector.flatten]
  simp [List.Vector.drop]
  simp [List.Vector.take]
  simp [GetElem.getElem]
  simp [List.Vector.get]
  have hi : i < m := by simp
  induction m with
  | zero =>
    contradiction
  | succ m ih =>
    let ⟨i, hi⟩ := i
    match i with
    | 0 =>
      simp
      unfold List.flatten
      match h_v : v.toList with
      | [] =>
        have h' : v.toList.length = m + 1 := by simp
        rw [h_v] at h'
        contradiction
      | _ :: _ =>
        have h_Eq : v.toList = v.val := by
          rfl
        simp [← h_Eq]
        simp [h_v]
        simp [List.Vector.toList]
    | i + 1 =>
      simp at hi
      let i' : Fin m := ⟨i, hi⟩
      have ih := ih v.tail i' (by simp)
      simp
      have h_val_length : v.val.length = m + 1 := by simp
      have h_tail_length : v.tail.val.length = m := by simp
      have h_Cons : v.val[i + 1].val = v.tail.val[i].val := by
        simp
      rw [h_Cons]
      have h_v := Eq_Cons_Tail v
      have h_v := UFn.of.Eq h_v List.Vector.toList
      erw [h_v]
      simp only [GetElem.getElem] at ih ⊢
      rw [ih]
      simp
      rw [Nat.succ_mul, Nat.add_comm (i * n) n]
      rw [Drop_Add.eq.DropDrop]
      rw [h_v]
      simp [List.Vector.toList_cons, List.map_cons, List.flatten_cons, i']


-- created on 2025-05-08
-- updated on 2026-11-20
