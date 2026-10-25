/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.FredholmAlternative
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Topology.Sequences
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Def.v1.Atlas.IntroductionToFunctionalAnalysis.code.SpectralTheory
open Function Set Filter Bornology Metric Pointwise Topology


namespace SpectralTheory

section AdjointOperator

variable {𝕜 : Type*} [RCLike 𝕜]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The Hilbert space $L^2([0,1])$ of square-integrable real-valued functions on
the unit interval, equipped with the restriction of Lebesgue measure to $[0,1]$. -/
noncomputable abbrev L2UnitInterval :=
  Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))

end AdjointOperator
end SpectralTheory
