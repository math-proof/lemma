module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortGeometry.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part12


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortCircle.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open SimpleGraph


noncomputable def kwAngularUnit (a : ℝ) : ℂ :=
  Complex.exp ((a : ℂ) * Complex.I)

end StatMech.FrontierA
