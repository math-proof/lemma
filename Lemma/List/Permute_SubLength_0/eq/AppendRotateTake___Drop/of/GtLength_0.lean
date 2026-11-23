import Theorem.List.Cons.eq.Append
import Theorem.List.AppendAppend.eq.Append_Append
import Theorem.List.Append.of.Eq
import Lemma.List.Rotate.eq.AppendDrop__Take.of.GeLength
import Theorem.List.EqPermute
import Lemma.Int.NegSucc.eq.NegAdd_1
import Theorem.Nat.AddAdd.eq.Add_Add
import Theorem.Nat.EqMin.of.Le
import Theorem.List.Drop_SubLength_1.eq.ListGet.of.GtLength_0
import Lemma.List.LengthDrop.eq.SubLength
import Theorem.Nat.EqSub_Sub.of.Ge
import Lemma.Nat.SubSub
import Theorem.Nat.EqMin.of.Gt
import Theorem.Nat.Sub.eq.Zero.of.Lt
import Theorem.List.Slice_0.eq.Take
import Theorem.Nat.AddSub.eq.Sub_Sub.of.Ge.Ge
import Theorem.Nat.LeSubS.of.Le
import Theorem.Nat.LtSubS.of.Lt.Le
open List Nat Int


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  (d : ℕ) :
-- imply
  let d' := s.length - 1 - d
  s.permute ⟨s.length - 1, by simp_all⟩ (-(d : ℕ)) = s.take d' ++ (s.drop d').rotate (d ⊓ (s.length - 1)) := by
-- proof
  intro d'
  simp [d']
  match d with
  | 0 =>
    simp
    rw [EqPermute]
  | d + 1 =>
    unfold List.permute
    simp
    match h : -1 + -(d : ℤ) with
    | Int.ofNat d =>
      grind
    | Int.negSucc d =>
      simp_all
      rw [Cons.eq.Append]
      rw [Append_Append.eq.AppendAppend]
      simp_all
      rw [NegSucc.eq.NegAdd_1] at h
      simp at h
      subst h
      rw [SubSub.eq.Sub_Add]
      rw [Add.comm]
      apply Append.of.Eq.left
      rw [EqAddSub.of.Ge (by linarith)]
      rw [Drop.eq.Nil]
      simp
      rw [AddAdd.eq.Add_Add]
      norm_num
      if h_i : s.length ≥ d + 2 then
        have h_i' := LeSubS.of.Le h_i 1
        simp at h_i'
        rw [Rotate.eq.AppendDrop__Take.of.GeLength]
        ·
          simp
          rw [EqMin.of.Le h_i']
          rw [AddSub.eq.Sub_Sub.of.Ge.Ge (by linarith) (by linarith)]
          simp
          rw [Drop_SubLength_1.eq.ListGet.of.GtLength_0 (by linarith)]
          simp
          unfold List.slice List.array_slice Function.comp
          congr
          rw [SubSub.comm]
          rw [EqSub_Sub.of.Ge (by assumption)]
          simp
        ·
          rw [LengthDrop.eq.SubLength]
          rw [EqSub_Sub.of.Ge (by assumption)]
          rw [EqMin.of.Le (by assumption)]
          simp
      else
        simp at h_i
        rw [EqMin.of.Gt (by omega)]
        rw [Sub.eq.Zero.of.Lt h_i]
        simp
        rw [Slice_0.eq.Take]
        rw [Cons.eq.Append]
        rw [← Drop_SubLength_1.eq.ListGet.of.GtLength_0 (by linarith)]
        rw [Rotate.eq.AppendDrop__Take.of.GeLength (by simp_all)]


-- created on 2025-06-17
-- updated on 2026-11-23
