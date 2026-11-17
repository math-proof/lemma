/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ComplexAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.OpenMapping
public import Structure.v1.Atlas.NumberTheoryI.code.ComplexAnalysis

@[expose] public section

open Complex Set Filter Finset MeasureTheory Topology Metric


instance : CoeFun ParameterizedCurve (fun _ => ℝ → ℂ) where
  coe := ParameterizedCurve.toFun

