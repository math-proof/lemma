module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.SummableUniformlyOn
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

@[expose] public section

open scoped BigOperators Topology ENNReal NNReal
open Metric


/-!
# Mittag-Leffler theorem (prescribed principal parts on `ℂ`)
-/


section

namespace Complex.MittagLefflerWanted

/-- Finite principal part at `s` given by finitely supported `coeff`. -/
noncomputable def principalPart (s : ℂ) (coeff : ℕ →₀ ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ coeff.support, coeff k * (z - s) ^ (-(↑k + 1) : ℤ)

end Complex.MittagLefflerWanted
end
