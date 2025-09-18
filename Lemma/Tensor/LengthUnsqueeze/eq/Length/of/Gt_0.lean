import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Algebra.LengthInsertIdx.eq.Add1Length.of.Le_Length
import Lemma.Algebra.LengthInsertIdx.eq.Length.of.Gt_Length
import Lemma.Logic.EqUFnS.of.Eq
import Lemma.Algebra.InsertIdxCons.eq.Cons_InsertIdx.of.Gt_0
import Lemma.Algebra.Ge_1.of.Gt_0
import Lemma.Algebra.Eq.of.Ge.Le
open Tensor Algebra Logic


@[main]
private lemma main
-- given
  (h : d > 0)
  (X : Tensor α s) :
-- imply
  (X.unsqueeze d).length = X.length := by
-- proof
  match s with
  | [] =>
    simp [Tensor.length]
    match h_insert : [].insertIdx d 1, h_d : X.unsqueeze d with
    | [], t =>
      simp
    | length :: tail, t =>
      simp
      have := EqUFnS.of.Eq h_insert List.length
      simp at this
      rw [LengthInsertIdx.eq.Length.of.Gt_Length] at this
      ·
        simp at this
      ·
        simp
        linarith
  | s₀ :: s =>
    rw [Length.eq.Get_0.of.GtLength_0]
    ·
      rw [Length.eq.Get_0.of.GtLength_0 (by simp)]
      simp_all [InsertIdxCons.eq.Cons_InsertIdx.of.Gt_0]
    ·
      by_cases h : d ≤ (s₀ :: s).length
      ·
        rw [LengthInsertIdx.eq.Add1Length.of.Le_Length (by simpa)]
        simp
      ·
        simp at h
        rw [LengthInsertIdx.eq.Length.of.Gt_Length (by assumption)]
        simp


-- created on 2025-07-12
