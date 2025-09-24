import Lemma.Algebra.EqEraseIdx.of.Ge_Length
import Lemma.Tensor.CastDiv.eq.DivCast.of.Eq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataDiv.eq.DivData
import Lemma.Vector.CastSum.eq.DivCastSumSplitAt_1
import Lemma.Tensor.ToVectorDiv.eq.DivToVector_Broadcast
import Lemma.Vector.MapMap.eq.Map_Comp
open Algebra Tensor Vector


@[main]
private lemma main
  [DivisionSemiring α]
-- given
  (X : Tensor α s)
  (n : Tensor α [])
  (dim : ℕ) :
-- imply
  (X / n).sum dim = X.sum dim / n := by
-- proof
  unfold Tensor.sum
  by_cases h : dim < s.length
  <;> simp [h]
  ·
    match dim with
    | .zero =>
      apply Eq.of.EqDataS
      let ⟨data⟩ := X
      repeat rw [DataDiv.eq.DivData]
      simp_all [CastSum.eq.DivCastSumSplitAt_1]
    | .succ dim =>
      simp
      match s with
      | .nil =>
        contradiction
      | s₀ :: s =>
        rw [ToVectorDiv.eq.DivToVector_Broadcast]
        simp [HDiv.hDiv]
        apply Eq.of.EqDataS
        simp
        sorry
  ·
    simp at h
    have h := EqEraseIdx.of.Ge_Length h
    rw [CastDiv.eq.DivCast.of.Eq.scalar h.symm X]


-- created on 2025-09-21
-- updated on 2025-09-24
