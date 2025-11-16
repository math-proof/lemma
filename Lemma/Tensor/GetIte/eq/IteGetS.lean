import sympy.tensor.tensor
import Lemma.Tensor.EqLengthS
import Lemma.Tensor.LengthIte.eq.Length
open Tensor


@[main]
private lemma left
  [Decidable p]
-- given
  (A B : Tensor α s)
  (i : Fin A.length) :
-- imply
  have : i < B.length := by simp [EqLengthS B A]
  have : i < (if p then
    A
  else
    B).length := by simp [LengthIte.eq.Length.left]
  (if p then
    A[i]
  else
    B[i]) = (if p then
    A
  else
    B)[i] := by
-- proof
  split_ifs with h <;> rfl


@[main]
private lemma right
  [Decidable p]
-- given
  (A B : Tensor α s)
  (i : Fin B.length) :
-- imply
  have : i < A.length := by simp [EqLengthS A B]
  have : i < (if p then
    A
  else
    B).length := by simp [LengthIte.eq.Length]
  (if p then
    A[i]
  else
    B[i]) = (if p then
    A
  else
    B)[i] := by
-- proof
  split_ifs with h <;> rfl


@[main]
private lemma main
  [Decidable p]
-- given
  (A B : Tensor α s)
  (i : Fin (if p then
    A
  else
    B).length) :
-- imply
  have h_i := i.isLt
  have : i < A.length := by
    simp [LengthIte.eq.Length.left] at h_i
    assumption
  have : i < B.length := by
    simp [LengthIte.eq.Length] at h_i
    assumption
  (if p then
    A
  else
    B)[i] = if p then
    A[i]
  else
    B[i] := by
-- proof
  split_ifs with h <;> rfl


@[main]
private nonrec lemma fin.left
  [Decidable p]
-- given
  (A B : Tensor α s)
  (i : Fin A.length) :
-- imply
  (if p then
    A.get i
  else
    B.get ⟨i, by simp [EqLengthS B A]⟩) = (if p then
    A
  else
    B).get ⟨i, by simp [LengthIte.eq.Length.left]⟩ := by
-- proof
  apply left


@[main]
private nonrec lemma fin.right
  [Decidable p]
-- given
  (A B : Tensor α s)
  (i : Fin B.length) :
-- imply
  (if p then
    A.get ⟨i, by simp [EqLengthS A B]⟩
  else
    B.get i) = (if p then
    A
  else
    B).get ⟨i, by simp [LengthIte.eq.Length]⟩ := by
-- proof
  apply right


@[main]
private nonrec lemma fin
  [Decidable p]
-- given
  (A B : Tensor α s)
  (i : Fin (if p then
    A
  else
    B).length)
  (h_i := i.isLt) :
-- imply
  (if p then
    A
  else
    B).get i = if p then
    A.get ⟨i, by
      simp [LengthIte.eq.Length.left] at h_i
      assumption
    ⟩
  else
    B.get ⟨i, by
      simp [LengthIte.eq.Length] at h_i
      assumption
    ⟩ := by
-- proof
  apply main


-- created on 2025-10-09
