import Lemma.List.Permute.eq.Ite
import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.List.LengthCons.eq.Add1Length
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.List.LengthDrop.eq.SubLength
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Algebra.Le_Min.of.Le.Le
import Lemma.Algebra.LeAdd_1
import Lemma.Algebra.Min
import Lemma.Algebra.EqAddMin__Sub
import Lemma.Int.NegSucc.eq.NegAdd_1
import Lemma.Algebra.EqAddS.is.Eq
import Lemma.Algebra.SubAdd.eq.Add_Sub.of.Ge
import Lemma.Nat.SubSub
import Lemma.Nat.EqSubAdd
open Algebra List Nat Int


@[main]
private lemma main
-- given
  (a : List α)
  (i : Fin a.length)
  (d : ℤ) :
-- imply
  (a.permute i d).length = a.length := by
-- proof
  rw [Permute.eq.Ite]
  split_ifs with h <;>
    rw [LengthAppend.eq.AddLengthS] <;>
    rw [LengthAppend.eq.AddLengthS] <;>
    rw [LengthCons.eq.Add1Length] <;>
    rw [LengthTake.eq.Min_Length] <;>
    rw [LengthDrop.eq.SubLength] <;>
    rw [LengthSlice.eq.SubMin] <;>
    simp_all
  ·
    match d with
    | .ofNat d =>
      contradiction
    | .negSucc d =>
      rw [NegSucc.eq.NegAdd_1]
      simp_all
      rw [Min.comm]
      have := EqAddMin__Sub a.length (i - (d + 1))
      apply Eq.symm
      apply Eq.trans this.symm
      rw [AddAdd.eq.Add_Add]
      apply EqAddS.of.Eq.left
      rw [Add_Sub.eq.SubAdd.of.Ge]
      ·
        rw [Add.comm (b := a.length)]
        rw [Add_Add.eq.AddAdd]
        rw [Add_Sub.eq.SubAdd.of.Ge (by simp_all)]
        rw [AddAdd.eq.Add_Add]
        rw [Add.comm (a := 1)]
        rw [SubSub.comm]
        rw [EqSubAdd]
      ·
        apply LeAdd_1
  ·
    match d with
    | .ofNat d =>
      simp_all
      rw [Add.comm (a := (i : ℕ))]
      rw [Add_Add.eq.AddAdd]
      rw [AddAdd.eq.Add_Add (c := 1)]
      rw [EqAddSub.of.Ge]
      ·
        rw [Min.comm]
        apply EqAddMin__Sub
      ·
        apply Le_Min.of.Le.Le
        ·
          linarith
        ·
          apply LeAdd_1
    | .negSucc d =>
      contradiction


-- created on 2025-06-07
