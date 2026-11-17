/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture21.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

open Complex Nat Filter Topology MeasureTheory Set


def truncatedLaplaceTransform (f : ℝ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..T, Complex.exp (-z * ↑t) * f t

