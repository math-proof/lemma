/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Def.v1.Atlas.ComplexVariables.code.Lecture13.Part2
import Lemma.Complex.Atlas.v1.ComplexVariables.code.Lecture13
import Abbrev.v1.Atlas.ComplexVariables.code.Lecture16
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

