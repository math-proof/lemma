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
open Complex InnerProductSpace Laplacian Metric Real Set Topology Filter MeasureTheory


abbrev IsHarmonic (u : ℂ → ℝ) (Ω : Set ℂ) : Prop :=
  InnerProductSpace.HarmonicOnNhd u Ω

