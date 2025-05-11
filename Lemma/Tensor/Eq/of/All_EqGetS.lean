import sympy.sets.sets
import Lemma.Tensor.Eq.of.EqDataS
import Lemma.Tensor.Eq.is.EqDataS
open Tensor


@[main]
private lemma main
  [Inhabited α]
  {a b : Tensor α (s₀ :: s)}
-- given
  (h : ∀ i ∈ range s₀, a[i] = b[i]) :
-- imply
  a = b := by
-- proof
  apply Eq.of.EqDataS
  simp [Eq.is.EqDataS] at h
  sorry


-- created on 2025-05-06
