import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.List.LengthCons.eq.Add1Length
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.Algebra.Lt.of.Lt.Lt
import Lemma.Nat.Le.of.Lt
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.LeAdd_1.of.Lt
open Algebra List Nat


@[main]
private lemma main
  {a : List α}
  {i j : ℕ}
-- given
  (h₀ : i < j)
  (h₁ : j < a.length) :
-- imply
  (a.take i ++ a[j] :: a.slice (i + 1) j ++ a[i] :: a.drop (j + 1)).length = a.length := by
-- proof
  rw [LengthAppend.eq.AddLengthS, LengthAppend.eq.AddLengthS]
  rw [LengthCons.eq.Add1Length, LengthCons.eq.Add1Length]
  rw [LengthTake.eq.Min_Length]
  have h_i := Lt.of.Lt.Lt h₀ h₁
  simp [Le.of.Lt h_i]
  rw [LengthSlice.eq.SubMin]
  simp [Le.of.Lt h₁]
  rw [Add_Add.eq.AddAdd, Add_Add.eq.AddAdd]
  rw [EqAdd_Sub.of.Ge h₀]
  have h_j := LeAdd_1.of.Lt h₁
  rw [EqAdd_Sub.of.Ge h_j]


-- created on 2025-05-15
