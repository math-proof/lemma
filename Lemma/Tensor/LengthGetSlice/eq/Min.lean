import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Algebra.LengthSlice.eq.Min
open Tensor Algebra


@[main]
private lemma main
-- given
  (X : Tensor α (s₀ :: s))
  (n : ℕ) :
-- imply
  X[:n].length = n ⊓ s₀ := by
-- proof
  unfold Tensor.getSlice
  repeat rw [Length.eq.Get_0.of.GtLength_0 (by simp)]
  simp
  apply LengthSlice.eq.Min


-- created on 2025-08-04
