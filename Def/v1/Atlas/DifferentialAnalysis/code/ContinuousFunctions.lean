/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

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

end ContinuousFunctions
