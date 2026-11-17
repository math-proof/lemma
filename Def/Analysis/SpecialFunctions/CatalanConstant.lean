/-
# Catalan's constant
-/

module

public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace Real

/-- Catalan's constant, defined by its alternating reciprocal odd-square
series `∑ n, (-1)^n / (2n+1)^2`. -/
noncomputable def catalanConstant : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2

end Real
