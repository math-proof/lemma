/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BellTuranIdentity.lean -/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular

namespace MetaMathlibExt

/-- Dobiński sum: `∑' k, k ^ m / k !`. -/
private noncomputable def dobinskiSum (m : ℕ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) ^ m / (k.factorial : ℝ)

/-- summand of the regrouped double sum, in the exact shape of the goal. -/
private noncomputable def fiberTerm (m s k : ℕ) : ℝ :=
  (((k : ℝ) ^ (m + 1) * ((s - k : ℕ) : ℝ) ^ (m + 1))
    / ((Nat.factorial k : ℝ) * (Nat.factorial (s - k) : ℝ)))
    * (((s : ℝ) - 2 * (k : ℝ)) ^ 2)
end MetaMathlibExt
