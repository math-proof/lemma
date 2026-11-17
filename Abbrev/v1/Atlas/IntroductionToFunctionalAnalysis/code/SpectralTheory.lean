/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Compact
public import Mathlib.Analysis.Normed.Operator.FredholmAlternative
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Def.v1.Atlas.IntroductionToFunctionalAnalysis.code.SpectralTheory
@[expose] public section

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
