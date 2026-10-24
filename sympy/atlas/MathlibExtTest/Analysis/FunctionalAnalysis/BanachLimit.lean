/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/FunctionalAnalysis/BanachLimit.lean -/

/-
Author: @toskua, Avocado
-/

import sympy.atlas.Analysis.FunctionalAnalysis.BanachLimit
import Lemma.Filter.Any_And_Eq_1AndAll_EqAndAll_Eq
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic


namespace MathlibExt.Analysis.FunctionalAnalysis.BanachLimitTest

open Filter
open scoped BoundedContinuousFunction ContinuousLinearMap

/-- Obtain a Banach-limit witness from the proved existence theorem. -/
noncomputable def witness : (ℕ →ᵇ ℝ) →L[ℝ] ℝ :=
  Classical.choose MathlibExt.Analysis.FunctionalAnalysis.BanachLimit.banach_limit

/-- Positivity: the witness is nonnegative on pointwise-nonnegative sequences. -/
example (f : ℕ →ᵇ ℝ) (h : ∀ n, 0 ≤ f n) : 0 ≤ witness f :=
  witness_spec.1 f h

/-- Normalization: the witness sends the constant-one sequence to `1`. -/
example : witness (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1 :=
  witness_spec.2.1

/-- Shift invariance: the witness agrees on a sequence and its left shift. -/
example (f g : ℕ →ᵇ ℝ) (h : ∀ n, g n = f (n + 1)) : witness f = witness g :=
  witness_spec.2.2.1 f g h

/-- Convergence extension: the witness returns the ordinary limit. -/
example (f : ℕ →ᵇ ℝ) (l : ℝ) (h : Tendsto (fun n => f n) atTop (nhds l)) :
    witness f = l :=
  witness_spec.2.2.2 f l h

/-- The witness evaluates every constant sequence at its value. -/
example (c : ℝ) : witness (BoundedContinuousFunction.const ℕ c) = c :=
  witness_spec.2.2.2 _ _ tendsto_const_nhds

end MathlibExt.Analysis.FunctionalAnalysis.BanachLimitTest
