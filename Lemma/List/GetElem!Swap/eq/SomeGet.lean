import Lemma.List.LengthSwap.eq.Length
import Lemma.Algebra.GetElem!.eq.SomeGet.of.Lt
import Lemma.Algebra.NotGt.is.Le
import Lemma.Logic.Ne.is.NotEq
import Lemma.Algebra.Lt.of.Le.Ne
import Lemma.Algebra.Ge.of.NotLt
import Lemma.Algebra.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
import Lemma.Algebra.Sub.gt.Zero.is.Lt
import Lemma.Algebra.LengthSlice.eq.SubMin
import Lemma.Algebra.Sub_Add.eq.SubSub
import Lemma.List.EqSwapS
open Algebra Logic List


@[main]
private lemma main
-- given
  (a : List α)
  (i j : Fin a.length) :
-- imply
  (a.swap i j)[i]? = some a[j] := by
-- proof
  have := LengthSwap.eq.Length a i j
  have h_i : i < (a.swap i j).length := by
    rw [this]
    simp
  have h_some := GetElem!.eq.SomeGet.of.Lt h_i
  simp [h_some]
  unfold List.swap
  split_ifs with h_eq h_lt? h_j h_i
  ·
    simp at h_eq
    simp [h_eq]
  ·
    simp
  ·
    have h_j := Ge.of.NotLt h_j
    have h_j : j < a.length := by simp
    contradiction
  ·
    have h_le := Le.of.NotGt h_lt?
    simp at h_eq
    have h_ne := Ne.of.NotEq h_eq
    have h_lt := Lt.of.Le.Ne h_ne.symm h_le
    simp_all
    rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0]
    ·
      have h_length_slice := LengthSlice.eq.SubMin a (j + 1) i
      rw [Sub_Add.eq.SubSub.nat] at h_length_slice
      simp [h_length_slice]
    ·
      apply Sub.gt.Zero.of.Lt.nat h_lt (α := ℕ)
  ·
    have h_i := Ge.of.NotLt h_i
    linarith


@[main]
private lemma left
-- given
  (a : List α)
  (i j : Fin a.length) :
-- imply
  (a.swap i j)[j]? = some a[i] := by
-- proof
  rw [EqSwapS]
  rw [main]


-- created on 2025-05-15
-- updated on 2025-05-17
