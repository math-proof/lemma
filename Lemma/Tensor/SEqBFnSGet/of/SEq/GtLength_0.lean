import Lemma.Tensor.EqGetS.of.Eq.Lt_Length
import Lemma.Algebra.LtVal
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEqBFnS.of.SEq
import Lemma.Logic.Eq.of.SEq
open Tensor Algebra Logic


@[main]
private lemma main
  {X : Tensor α s}
  {X' : Tensor α s'}
-- given
  (h : s.length > 0)
  (h_X : X ≃ X')
  (i : Fin s[0])
  (g : List ℕ → List ℕ)
  (f : (s : List ℕ) → Tensor α s → Tensor α (g s)) :
-- imply
  have : i < X.length := by
    rw [Length.eq.Get_0.of.GtLength_0 h]
    simp
  have h_s := h_X.left
  have : i < X'.length := by
    rw [h_s] at h
    rw [Length.eq.Get_0.of.GtLength_0 h]
    simp [← h_s]
  f s.tail X[i] ≃ f s'.tail X'[i] := by
-- proof
  have h_s0 := Length.eq.Get_0.of.GtLength_0 h X
  have h_X' := h_X.symm
  have h_i := LtVal i
  simp [← h_s0] at h_i
  have h_get := EqGetS.of.Eq.Lt_Length h_i h_X
  apply SEqBFnS.of.SEq h_get


-- created on 2025-07-13
