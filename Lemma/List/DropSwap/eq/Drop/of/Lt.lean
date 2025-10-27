import Lemma.List.Cons.eq.Append
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.EqDropAppend.of.Eq_Length
import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.List.LengthList.eq.One
import Lemma.Nat.EqAddS.is.Eq
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Nat.Lt.of.Lt.Lt
import Lemma.Nat.Le.of.Lt
import Lemma.Nat.Sub_Add.eq.SubSub
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqAdd_Sub.of.Lt
import Lemma.Nat.Sub.ge.One.of.Lt
open List Nat


@[main]
private lemma main
  {i j : ℕ}
-- given
  (h : i < j)
  (a : List α) :
-- imply
  (a.swap i j).drop (j + 1) = a.drop (j + 1) := by
-- proof
  unfold List.swap
  split_ifs with h_eq h_j
  ·
    rfl
  ·
    rw [Cons.eq.Append a[i]]
    rw [Append_Append.eq.AppendAppend]
    apply EqDropAppend.of.Eq_Length
    rw [LengthAppend.eq.AddLengthS]
    rw [LengthList.eq.One]
    apply EqAddS.of.Eq
    simp
    rw [LengthSlice.eq.SubMin]
    have h_i := Lt.of.Lt.Lt h h_j
    simp [Le.of.Lt h_i, Le.of.Lt h_j]
    rw [Sub_Add.eq.SubSub]
    rw [EqAddSub.of.Ge]
    ·
      rw [EqAdd_Sub.of.Lt h]
    ·
      apply Sub.ge.One.of.Lt h
  ·
    rfl


-- created on 2025-05-17
-- updated on 2025-05-18
