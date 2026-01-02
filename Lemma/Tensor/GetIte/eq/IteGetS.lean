import sympy.tensor.tensor
import Lemma.Tensor.EqLengthS
import Lemma.Tensor.LengthIte.eq.Length
open Tensor


@[main, fin]
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


@[main, fin]
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


@[main, fin]
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


-- created on 2025-10-09
