/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Theorem.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition


namespace ContinuousFunctions

open ContinuousLinearMap

section PosPartConstruction

variable {X : Type*} [MetricSpace X]

/-- The pointwise minimum of two `C₀` functions, again in `C₀(X, ℝ)`. -/
noncomputable def c0min (f g : C₀Map X) : C₀Map X where
  toFun := fun x => min (f x) (g x)
  continuous_toFun := (map_continuous f).min (map_continuous g)
  zero_at_infty' := by
    have := (zero_at_infty f).min (zero_at_infty g)
    simp only [min_self] at this; exact this

/-- For a functional `u` and `f ∈ C₀(X, ℝ)`, the set of values `u g` ranging over `g` with
`0 ≤ g ≤ f` pointwise. The supremum of this set defines the positive part `u⁺(f)`. -/
def posPartSet (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) : Set ℝ :=
  {r | ∃ g : C₀Map X, (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ f x) ∧ r = u g}

end PosPartConstruction
end ContinuousFunctions
