import Lemma.Tensor.Slice.of.Slice.Eq.Lt
import sympy.Basic
open Tensor

set_option maxHeartbeats 500000


@[main]
private lemma main
  {X Y : Tensor α (s₀ :: s)}
-- given
  (h_n : n < s₀)
  (h₀ : X[:n] = Y[:n])
  (h₁ : X[n] = Y[n]) :
-- imply
  X[:(n + 1 : ℕ)] = Y[:(n + 1 : ℕ)] := by
-- proof
  exact Slice.of.Slice.Eq.Lt h_n h₀ h₁


-- created on 2026-10-03
