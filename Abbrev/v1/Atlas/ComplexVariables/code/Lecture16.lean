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
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
public import Def.v1.Atlas.ComplexVariables.code.Lecture13.Part2
public import Theorem.Complex.Atlas.v1.ComplexVariables.code.Lecture13
@[expose] public section

open Complex InnerProductSpace Laplacian Metric Real Set Topology Filter MeasureTheory


abbrev IsHarmonic (u : ℂ → ℝ) (Ω : Set ℂ) : Prop :=
  InnerProductSpace.HarmonicOnNhd u Ω

