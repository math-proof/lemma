/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Lipschitz
import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions
open Set Filter Topology
open scoped ZeroAtInfty


namespace ContinuousFunctions

/-- Pointwise evaluation of the positive part: `f⁺(x) = max(f(x), 0)`. -/
@[simp]
theorem posPart_apply (f : C₀(X, ℝ)) (x : X) :
    zeroAtInftyPosPart f x = max (f x) 0 := rfl

/-- Pointwise evaluation of the negative part: `f⁻(x) = max(-f(x), 0)`. -/
@[simp]
theorem negPart_apply (f : C₀(X, ℝ)) (x : X) :
    zeroAtInftyNegPart f x = max (-f x) 0 := rfl

/-- Decomposition `f = f⁺ - f⁻` in `C₀(X, ℝ)`. -/
theorem decompose_pos_neg (f : C₀(X, ℝ)) :
    f = zeroAtInftyPosPart f - zeroAtInftyNegPart f := by
  ext x
  simp only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, posPart_apply, negPart_apply]
  exact (max_zero_sub_max_neg_zero_eq_self (f x)).symm

/-- Pointwise bound: `f⁺(x) ≤ |f(x)|`. -/
theorem posPart_le_abs (f : C₀(X, ℝ)) (x : X) :
    zeroAtInftyPosPart f x ≤ |f x| := by
  simp only [posPart_apply]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- Pointwise bound: `f⁻(x) ≤ |f(x)|`. -/
theorem negPart_le_abs (f : C₀(X, ℝ)) (x : X) :
    zeroAtInftyNegPart f x ≤ |f x| := by
  simp only [negPart_apply]
  exact max_le (neg_le_abs _) (abs_nonneg _)

/-- Nonnegativity of the positive part: `0 ≤ f⁺(x)`. -/
theorem posPart_nonneg (f : C₀(X, ℝ)) (x : X) :
    0 ≤ zeroAtInftyPosPart f x := le_max_right _ _

/-- Nonnegativity of the negative part: `0 ≤ f⁻(x)`. -/
theorem negPart_nonneg (f : C₀(X, ℝ)) (x : X) :
    0 ≤ zeroAtInftyNegPart f x := le_max_right _ _

end ContinuousFunctions
