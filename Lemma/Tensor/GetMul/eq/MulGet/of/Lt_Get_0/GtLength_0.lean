import Lemma.Tensor.GetMul.eq.MulGet
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Tensor


@[main]
private lemma main
  [Mul α]
-- given
  (h : s.length > 0)
  (h_i : i < s[0])
  (X : Tensor α s)
  (a : α):
-- imply
  have : i < (X * a).length := by rwa [Length.eq.Get_0.of.GtLength_0]
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X * a)[i] = X[i] * a := by
-- proof
  cases s with
  | nil =>
    contradiction
  | cons s₀ s =>
    simp at h
    let i' : Fin s₀ := ⟨i, h_i⟩
    have h_i : i' = i := rfl
    have := GetMul.eq.MulGet X a i'
    simp_all


@[main]
private lemma fin
  [Mul α]
-- given
  (h : s.length > 0)
  (h_i : i < s[0])
  (X : Tensor α s)
  (a : α):
-- imply
  (X * a).get ⟨i, by rwa [Length.eq.Get_0.of.GtLength_0]⟩ = X.get ⟨i, by rwa [Length.eq.Get_0.of.GtLength_0]⟩ * a := by
-- proof
  apply main h h_i


-- created on 2025-12-06
