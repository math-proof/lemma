/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Def.v1.Atlas.ComplexVariables.code.Lecture13


@[expose] public noncomputable section

open Complex MeasureTheory Set intervalIntegral Real Filter Function Topology Metric

namespace ClosedCurve

variable (γ : ClosedCurve)

abbrev RiemannSphere := OnePoint ℂ

end ClosedCurve
end
