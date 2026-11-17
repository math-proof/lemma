/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BellTuranIdentity.lean -/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

namespace MetaMathlibExt

/-- Dobiński sum: `∑' k, k ^ m / k !`. -/
noncomputable def dobinskiSum (m : ℕ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) ^ m / (k.factorial : ℝ)

/-- summand of the regrouped double sum, in the exact shape of the goal. -/
noncomputable def fiberTerm (m s k : ℕ) : ℝ :=
  (((k : ℝ) ^ (m + 1) * ((s - k : ℕ) : ℝ) ^ (m + 1))
    / ((Nat.factorial k : ℝ) * (Nat.factorial (s - k) : ℝ)))
    * (((s : ℝ) - 2 * (k : ℝ)) ^ 2)

end MetaMathlibExt
