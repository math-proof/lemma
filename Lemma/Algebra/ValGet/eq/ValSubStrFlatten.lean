import stdlib.List.Vector
import Lemma.Algebra.Eq_Cons_Tail
import Lemma.Algebra.GetCons__Add_1.eq.Get
import Lemma.Algebra.FlattenMapToListCons.eq.Append_FlattenMapToList
import Lemma.Algebra.MulAdd_1.eq.Add_Mul
import Lemma.Algebra.Drop_Add.eq.DropDrop
import Lemma.Algebra.EqDropAppend__Length
import Lemma.Logic.EqFunS.of.Eq
open Algebra Logic


@[main]
private lemma main
  [Inhabited α]
-- given
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m) :
-- imply
  v[i].val = (v.flatten.substr (i * n) n).val := by
-- proof
  simp [List.Vector.substr]
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
    | .zero =>
      simp
      unfold List.flatten
      match h_v : v.toList with
      | [] =>
        have h' : v.toList.length = m + 1 := by simp
        rw [h_v] at h'
        contradiction
      | head :: tail =>
        simp [List.take]
        have h_Eq : v.toList = v.val := by
          rfl
        simp [← h_Eq]
        simp [h_v]
        simp [List.Vector.toList]
    | .succ i =>
      simp at hi
      let i' : Fin m := ⟨i, hi⟩
      have ih := ih v.tail i' (by simp)
      have h_i : i = i' := by rfl
      simp
      have h_Cons := GetCons__Add_1.eq.Get v[0] v.tail i
      have h_val_length : v.val.length = m + 1 := by
        simp
      have h_tail_length : v.tail.val.length = m := by
        simp
      have h_Cons : v.val[i + 1].val = v.tail.val[i].val := by
        simp [h_Cons]
      rw [h_Cons]
      have h_v := Eq_Cons_Tail v
      have h_v := EqFunS.of.Eq h_v (List.Vector.toList)
      rw [h_v]
      simp only [GetElem.getElem]
      simp only [GetElem.getElem] at ih
      rw [ih]
      rw [FlattenMapToListCons.eq.Append_FlattenMapToList]
      simp
      rw [MulAdd_1.eq.Add_Mul]
      rw [Drop_Add.eq.DropDrop]
      have : (List.drop n (v.head.toList ++ (List.map List.Vector.toList v.tail.toList).flatten)) = (List.drop v.head.toList.length (v.head.toList ++ (List.map List.Vector.toList v.tail.toList).flatten)) := by
        simp
      rw [this]
      rw [EqDropAppend__Length]


-- created on 2025-05-08
-- updated on 2025-05-10
