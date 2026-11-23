/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
public import Def.v1.Atlas.ComplexVariables.code.Lecture13.Part2
public import Theorem.Complex.Atlas.v1.ComplexVariables.code.Lecture13
public import Abbrev.v1.Atlas.ComplexVariables.code.Lecture16

@[expose] public section

open Complex InnerProductSpace Laplacian Metric Real Set Topology Filter MeasureTheory


def poissonIntegral (U : ℂ → ℝ) (a : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel 0 a • U) 0 1

def herglotzIntegral (U : ℂ → ℝ) (a : ℂ) : ℂ :=
  (2 * (π : ℝ))⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
    herglotzRieszKernel 0 a (circleMap 0 1 θ) • (U (circleMap 0 1 θ) : ℂ)

noncomputable def mobiusTransform (a z : ℂ) : ℂ :=
  (z + a) / (starRingEnd ℂ a * z + 1)

noncomputable def invMobiusAngle (a : ℂ) (_ha : a ∈ ball (0 : ℂ) 1) : ℝ → ℝ :=
  fun θ => Complex.arg ((1 - a) / (1 - starRingEnd ℂ a)) +
    ∫ t in (0 : ℝ)..θ, poissonKernel 0 a (circleMap 0 1 t)

