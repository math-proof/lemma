import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
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
