import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
open Tensor


@[main]
private lemma main
  [Mul α]
-- given
  (h : s.length > 0)
  (h_i : i < s[0])
  (A B : Tensor α s) :
-- imply
  have : i < (A * B).length := by rwa [Length.eq.Get_0.of.GtLength_0]
  have : i < A.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  have : i < B.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (A * B)[i] = A[i] * B[i] := by
-- proof
  cases s with
  | nil =>
    contradiction
  | cons s₀ s =>
    simp at h
    let i' : Fin s₀ := ⟨i, h_i⟩
    have h_i : i' = i := rfl
    have := GetMul.eq.MulGetS A B i'
    simp_all


@[main]
private lemma fin
  [Mul α]
-- given
  (h : s.length > 0)
  (h_i : i < s[0])
  (A B : Tensor α s) :
-- imply
  (A * B).get ⟨i, by rwa [Length.eq.Get_0.of.GtLength_0]⟩ = A.get ⟨i, by rwa [Length.eq.Get_0.of.GtLength_0]⟩ * B.get ⟨i, by rwa [Length.eq.Get_0.of.GtLength_0]⟩ := by
-- proof
  apply main h h_i A B


-- created on 2025-07-01
-- updated on 2025-07-13
