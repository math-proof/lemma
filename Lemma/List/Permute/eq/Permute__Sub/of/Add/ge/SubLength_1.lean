import Lemma.List.Permute.eq.Ite
import Lemma.Algebra.Le_Sub_1
import Lemma.Algebra.Ge.of.Ge.Ge
import Lemma.Algebra.GeCoeS.is.Ge
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.Ge_1
import Lemma.Algebra.Lt.of.Sub.lt.Zero
import Lemma.Algebra.CoeSub_1.eq.SubCoe_1.of.Ge_1
import Lemma.Algebra.AddSub.eq.SubAdd
import Lemma.Algebra.EqAddSub
import Lemma.Nat.EqMax.of.Gt
import Lemma.Algebra.AddAdd.eq.Add_Add
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Int.EqToNat
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.Drop.eq.Nil
import Lemma.List.Slice.eq.Slice__Length.of.Ge_Length
open Algebra List Int Nat


@[main]
private lemma main
  {a : List α}
  {i : Fin a.length}
  {d : ℤ}
-- given
  (h : i + d ≥ a.length - 1) :
-- imply
  a.permute i d = a.permute i (a.length - 1 - i) := by
-- proof
  have hi := Le_Sub_1 i
  have h_length := Ge_1 i
  rw [Permute.eq.Ite]
  split_ifs with h_d
  ·
    have hi := GeCoeS.of.Ge.nat (R := ℤ) hi
    rw [CoeSub.eq.SubCoeS.of.Ge] at hi
    have h_ge := Ge.of.Ge.Ge h hi
    linarith
    assumption
  ·
    simp at h_d
    rw [Permute.eq.Ite]
    split_ifs with h_i
    ·
      have h_i := Lt.of.Sub.lt.Zero h_i
      rw [SubCoe_1.eq.CoeSub_1.of.Ge_1] at h_i
      linarith
      assumption
    ·
      simp
      have h_nat : (i + (a.length - 1 - i + 1 : ℤ).toNat) = a.length := by
        rw [AddSub.eq.SubAdd]
        rw [EqAddSub]
        rw [SubCoeS.eq.CoeSub.of.Ge]
        simp
        linarith
      rw [h_nat]
      have h_nat : i + (d + 1).toNat = i + d + 1 := by
        simp_all
        rw [EqMax.of.Gt]
        apply Add_Add.eq.AddAdd
        linarith
      have h_nat : i + (d + 1).toNat = (i + d + 1).toNat := by
        rw [← h_nat]
        rw [AddCoeS.eq.CoeAdd]
        apply EqToNat
      have h_ge : i + (d + 1).toNat ≥ a.length := by
        rw [h_nat]
        linarith
      rw [Drop.eq.Nil.of.Ge_Length]
      rw [Drop.eq.Nil]
      rwa [Slice.eq.Slice__Length.of.Ge_Length]
      assumption


-- created on 2025-06-07
