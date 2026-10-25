/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/FunctionSequences/PowerSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Normed.Group.FunctionSeries
open Filter Topology

open scoped NNReal ENNReal


namespace FunctionSequences

/-- A real power series about a center point `x₀`, given by a sequence of real coefficients
`a : ℕ → ℝ`. Formally, it represents the formal series `∑ₘ aₘ (x - x₀)^m`. -/
structure PowerSeries where
  a : ℕ → ℝ
  x₀ : ℝ

end FunctionSequences
