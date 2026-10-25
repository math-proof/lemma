/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Log


noncomputable section

open Complex MeasureTheory Set intervalIntegral Real Filter Function Topology Metric

structure ClosedCurve where
  toFun : ℝ → ℂ
  a : ℝ
  b : ℝ
  hab : a ≤ b
  continuous_toFun : ContinuousOn toFun (Icc a b)
  differentiable : DifferentiableOn ℝ toFun (Icc a b)
  continuous_deriv : ContinuousOn (deriv toFun) (Icc a b)
  closed : toFun a = toFun b

end
