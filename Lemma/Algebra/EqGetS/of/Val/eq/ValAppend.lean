import stdlib.List.Vector
import Lemma.Algebra.EqGetS.of.Eq.Lt.Lt
import Lemma.Algebra.ValAppend.eq.AppendValS
import Lemma.Algebra.LengthAppend.eq.AddLengthS
import Lemma.Algebra.Ge.of.NotLt
import Lemma.Logic.EqFunS.of.Eq
open Algebra Logic


@[main]
private lemma main
  [Inhabited α]
  {a : List.Vector α N}
  {b : List.Vector α m}
  {c : List.Vector α n}
-- given
  (h : a.val = (b ++ c).val)
  (i : Fin m) :
-- imply
  a[i] = b[i] := by
-- proof
  have h_a_length : a.val.length = N := by simp
  have h_b_length : b.val.length = m := by simp
  have h_c_length : c.val.length = n := by simp
  rw [ValAppend.eq.AppendValS] at h
  have h_a_length := EqFunS.of.Eq h List.length
  rw [LengthAppend.eq.AddLengthS] at h_a_length
  rw [h_b_length, h_c_length] at h_a_length
  have hi : i < m := by simp
  have h_a_length : i < a.val.length := by
    rw [h_a_length]
    linarith
  have h_bc_length : i < (b ++ c).val.length := by
    rw [ValAppend.eq.AppendValS]
    rw [LengthAppend.eq.AddLengthS]
    rw [h_b_length, h_c_length]
    linarith
  have h_Eq := EqGetS.of.Eq.Lt.Lt h_a_length h_bc_length h
  simp [ValAppend.eq.AppendValS] at h_Eq
  simp [GetElem.getElem]
  split_ifs with h
  ·
    simp [List.Vector.get]
    assumption
  ·
    have h := Ge.of.NotLt h
    linarith


-- created on 2025-05-10
