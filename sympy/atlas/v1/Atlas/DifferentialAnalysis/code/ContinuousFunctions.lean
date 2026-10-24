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

open Set Filter Topology
open scoped ZeroAtInfty

namespace ContinuousFunctions

/-- Positive part `f⁺ = max(f, 0)` of a real-valued continuous function vanishing at infinity,
itself in `C₀(X, ℝ)`. -/
noncomputable def zeroAtInftyPosPart (f : C₀(X, ℝ)) : C₀(X, ℝ) where
  toFun := fun x => max (f x) 0
  continuous_toFun := (map_continuous f).max continuous_const
  zero_at_infty' := by
    have h := (zero_at_infty f).max (tendsto_const_nhds (x := (0 : ℝ)))
    simp only [max_self] at h
    exact h

/-- Negative part `f⁻ = max(-f, 0)` of a real-valued continuous function vanishing at infinity,
itself in `C₀(X, ℝ)`. -/
noncomputable def zeroAtInftyNegPart (f : C₀(X, ℝ)) : C₀(X, ℝ) where
  toFun := fun x => max (-f x) 0
  continuous_toFun := ((map_continuous f).neg).max continuous_const
  zero_at_infty' := by
    have hnf : Tendsto (fun x => -f x) (cocompact X) (𝓝 0) := by
      simpa only [neg_zero] using (zero_at_infty f).neg
    have h := hnf.max (tendsto_const_nhds (x := (0 : ℝ)))
    simp only [max_self] at h
    exact h

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

/-- Two norms on `V` are equivalent if they are mutually controlled by a single positive
constant, i.e. `(1/C) · norm₁ v ≤ norm₂ v ≤ C · norm₁ v` for all `v`. -/
def AreEquivalentNorms {V : Type*} (norm₁ norm₂ : V → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ v : V, (1 / C) * norm₁ v ≤ norm₂ v ∧ norm₂ v ≤ C * norm₁ v

/-- Equivalence of norms on finite-dimensional vector spaces: any linear isomorphism between
finite-dimensional normed spaces gives rise to equivalent norms `v ↦ ‖v‖` and `v ↦ ‖e v‖`. -/
end NormedSpaces

open Bornology Metric Set

namespace ContinuousLinearFunctional

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
