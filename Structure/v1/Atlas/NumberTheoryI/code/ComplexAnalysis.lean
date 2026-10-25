/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ComplexAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.OpenMapping
import Def.v1.Atlas.NumberTheoryI.code.ComplexAnalysis
open Complex Set Filter Finset MeasureTheory Topology Metric


structure ParameterizedCurve where
  toFun : ℝ → ℂ
  a : ℝ
  b : ℝ
  hab : a ≤ b
  continuous_on : ContinuousOn toFun (Set.Icc a b)

