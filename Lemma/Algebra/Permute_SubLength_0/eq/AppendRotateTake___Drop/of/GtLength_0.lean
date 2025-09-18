import Lemma.Algebra.Cons.eq.Append
import Lemma.Algebra.AppendAppend.eq.Append_Append
import Lemma.Algebra.EqAppendS.of.Eq
import Lemma.Algebra.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.Algebra.EqPermute__0
import Lemma.Algebra.EqAddSub.of.Ge
import Lemma.Algebra.Drop.eq.Nil
import Lemma.Algebra.NegSucc.eq.NegAdd_1
import Lemma.Algebra.Sub_Add.eq.SubSub
import Lemma.Algebra.Add
import Lemma.Algebra.AddAdd.eq.Add_Add
import Lemma.Algebra.EqMin.of.Le
import Lemma.Algebra.Drop_SubLength_1.eq.ListGet.of.GtLength_0
import Lemma.Algebra.LengthDrop.eq.SubLength
import Lemma.Algebra.EqSub_Sub.of.Ge
import Lemma.Algebra.SubSub
import Lemma.Algebra.EqMin.of.Gt
import Lemma.Algebra.Sub.eq.Zero.of.Lt
import Lemma.Algebra.Slice_0.eq.Take
import Lemma.Algebra.AddSub.eq.Sub_Sub.of.Ge.Ge
import Lemma.Algebra.LeSubS.of.Le
import Lemma.Algebra.LtSubS.of.Lt.Le
open Algebra


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length > 0)
  (d : ℕ) :
-- imply
  let d' := a.length - 1 - d
  a.permute ⟨a.length - 1, by simp_all [h]⟩ (-(d : ℕ)) = a.take d' ++ (a.drop d').rotate (d ⊓ (a.length - 1)) := by
-- proof
  intro d'
  simp [d']
  match d with
  | .zero =>
    simp
    rw [EqPermute__0]
  | .succ d =>
    unfold List.permute
    simp
    match h : -1 + -(d : ℤ) with
    | Int.ofNat d =>
      simp_all
      linarith
    | Int.negSucc d =>
      simp_all
      rw [Cons.eq.Append]
      rw [Append_Append.eq.AppendAppend]
      simp_all
      rw [NegSucc.eq.NegAdd_1] at h
      simp at h
      subst h
      rw [SubSub.eq.Sub_Add.nat]
      rw [Add.comm]
      apply EqAppendS.of.Eq.left
      rw [EqAddSub.of.Ge (by linarith)]
      rw [Drop.eq.Nil]
      simp
      rw [AddAdd.eq.Add_Add]
      norm_num
      by_cases h_i : a.length ≥ d + 2
      ·
        have h_i' := LeSubS.of.Le.nat h_i 1
        simp at h_i'
        rw [Rotate.eq.AppendDrop__Take.of.Le_Length]
        ·
          simp
          rw [EqMin.of.Le h_i']
          rw [AddSub.eq.Sub_Sub.of.Ge.Ge (by linarith) (by linarith)]
          simp
          rw [Drop_SubLength_1.eq.ListGet.of.GtLength_0 (by linarith)]
          simp
          unfold List.slice List.array_slice Function.comp
          congr
          rw [SubSub.comm.nat]
          rw [EqSub_Sub.of.Ge (by assumption)]
          simp
        ·
          rw [LengthDrop.eq.SubLength]
          rw [EqSub_Sub.of.Ge (by assumption)]
          rw [EqMin.of.Le (by assumption)]
          simp
      ·
        simp at h_i
        have h_i' := LtSubS.of.Lt.Le (c := 1) (by assumption) h_i
        simp at h_i'
        rw [EqMin.of.Gt h_i']
        rw [Sub.eq.Zero.of.Lt h_i]
        simp
        rw [Slice_0.eq.Take]
        rw [Cons.eq.Append]
        rw [← Drop_SubLength_1.eq.ListGet.of.GtLength_0 (by linarith)]
        rw [Rotate.eq.AppendDrop__Take.of.Le_Length (by simp_all)]


-- created on 2025-06-17
-- updated on 2025-06-19
