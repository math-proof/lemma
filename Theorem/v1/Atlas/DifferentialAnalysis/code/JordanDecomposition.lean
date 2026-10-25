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
import Def.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition


namespace ContinuousFunctions

open ContinuousLinearMap

section PosPartConstruction

variable {X : Type*} [MetricSpace X]

/-- Pointwise evaluation of a `C₀` function is bounded by its sup norm. -/
lemma c0_eval_le_norm (f : C₀Map X) (x : X) : |f x| ≤ ‖f‖ := by
  have : ‖f.toBCF x‖ ≤ ‖f.toBCF‖ := BoundedContinuousFunction.norm_coe_le_norm f.toBCF x
  simp only [Real.norm_eq_abs] at this; exact this

/-- Monotonicity of the sup norm on nonnegative `C₀` functions: if `0 ≤ g ≤ f` pointwise then
`‖g‖ ≤ ‖f‖`. -/
lemma c0_norm_le_of_nonneg_le (f g : C₀Map X) (hg0 : ∀ x, 0 ≤ g x)
    (hgf : ∀ x, g x ≤ f x) : ‖g‖ ≤ ‖f‖ := by
  change ‖g.toBCF‖ ≤ ‖f.toBCF‖
  rw [BoundedContinuousFunction.norm_le (norm_nonneg f.toBCF)]
  intro x; show |g x| ≤ ‖f‖
  rw [abs_of_nonneg (hg0 x)]
  exact le_trans (hgf x) (le_trans (le_abs_self _) (c0_eval_le_norm f x))

end PosPartConstruction
end ContinuousFunctions
