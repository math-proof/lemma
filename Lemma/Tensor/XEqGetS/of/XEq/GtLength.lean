import Lemma.Tensor.EqLengthS
import Lemma.Tensor.XEq.is.All_XEqGetS
open Tensor


@[main, fin]
private lemma main
  [XEq α]
  {A B : Tensor α s}
  {i : ℕ}
-- given
  (h₀ : A.length > i)
  (h₁ : A ≈ B) :
-- imply
  A[i] ≈ B[i]'(by rwa [EqLengthS A B] at h₀) := by
-- proof
  match s with
  | [] =>
    simp [Tensor.length] at h₀
  | m :: s' =>
    exact All_XEqGetS.of.XEq h₁ ⟨i, by simp [Tensor.length] at h₀ ⊢; omega⟩


-- created on 2026-07-21
