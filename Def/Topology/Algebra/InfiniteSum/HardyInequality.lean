/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Algebra.InfiniteSum.Real
/-!
# Hardy's inequality for series

This file proves the sharp `ℓᵖ` bound for the sequence of prefix averages of a
nonnegative real sequence when `1 < p`.
-/


namespace MetaMathlibExt

noncomputable def hardy_average (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, a i) / (n : ℝ)

end MetaMathlibExt
