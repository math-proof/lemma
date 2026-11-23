/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions.Part2
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

@[expose] public section


/-- The space `C₀(X, ℝ)` of continuous real-valued functions on `X` vanishing at infinity. -/
abbrev C₀Map (X : Type*) [TopologicalSpace X] := ZeroAtInftyContinuousMap X ℝ

