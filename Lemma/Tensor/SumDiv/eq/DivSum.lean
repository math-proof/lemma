import sympy.tensor.tensor
import Lemma.Algebra.EqEraseIdx.of.Ge_Length
import Lemma.Tensor.CastDiv.eq.DivCast
import Lemma.Tensor.Eq.is.EqDataS
open Algebra Tensor


@[main]
private lemma main
  [Add α] [Zero α] [Div α] [NatCast α]
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
      simp
      apply Eq.of.EqDataS
      simp
      simp [HDiv.hDiv]
      let ⟨data⟩ := X
      simp
      sorry
    | .succ dim =>
      simp
      sorry
  ·
    simp at h
    rw [CastDiv.eq.DivCast.scalar]
    rw [EqEraseIdx.of.Ge_Length h]


-- created on 2025-09-21
