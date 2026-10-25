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
import Structure.v1.Atlas.RealAnalysis.code.FunctionSequences.PowerSeries
open Filter Topology

open scoped NNReal ENNReal


namespace FunctionSequences

/-- The `m`-th term of the power series `p` evaluated at `x`, i.e. `aₘ · (x - x₀)^m`. -/
def PowerSeries.term (p : PowerSeries) (x : ℝ) (m : ℕ) : ℝ :=
  p.a m * (x - p.x₀) ^ m

/-- The `n`-th partial sum of the power series `p` evaluated at `x`, i.e.
`∑_{m=0}^{n-1} aₘ (x - x₀)^m`. -/
def PowerSeries.partialSum (p : PowerSeries) (x : ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, p.term x m

/-- The radius of convergence `ρ` of a real power series with coefficients `a : ℕ → ℝ`,
defined via the Cauchy–Hadamard formula as the reciprocal of
`limsup_{n → ∞} ‖aₙ‖^(1/n)`, taking values in `ℝ≥0∞`. -/
noncomputable def radiusOfConvergence (a : ℕ → ℝ) : ENNReal :=
  (limsup (fun n => ((‖a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop)⁻¹

end FunctionSequences
