/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/FunctionSequences/PowerSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Analytic.RadiusLiminf
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public section

open Filter Topology

open scoped NNReal ENNReal


namespace FunctionSequences

/-- A real power series about a center point `x₀`, given by a sequence of real coefficients
`a : ℕ → ℝ`. Formally, it represents the formal series `∑ₘ aₘ (x - x₀)^m`. -/
structure PowerSeries where
  a : ℕ → ℝ
  x₀ : ℝ

end FunctionSequences
