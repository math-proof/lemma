/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GeodesicTriangles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Class.v1.Atlas.DifferentialGeometry.code.Geodesics
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Geodesics
import Structure.v1.Atlas.DifferentialGeometry.code.GeodesicTriangles
open scoped InnerProductSpace
open EuclideanGeometry


noncomputable section

namespace Geodesics

def GeodesicTriangle.sideA {X : Type*} [MetricSpace X] (T : GeodesicTriangle X) : ℝ :=
  dist T.p₂ T.p₃

def GeodesicTriangle.sideB {X : Type*} [MetricSpace X] (T : GeodesicTriangle X) : ℝ :=
  dist T.p₁ T.p₃

def GeodesicTriangle.sideC {X : Type*} [MetricSpace X] (T : GeodesicTriangle X) : ℝ :=
  dist T.p₁ T.p₂

def comparisonAngle {X : Type*} [MetricSpace X] (p₁ p₂ p₃ : X) : ℝ :=
  let a := dist p₂ p₃
  let b := dist p₁ p₃
  let c := dist p₁ p₂
  if b = 0 ∨ c = 0 then 0
  else Real.arccos ((b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c))

def GeodesicTriangle.comparisonAngleAt₁ {X : Type*} [MetricSpace X]
    (T : GeodesicTriangle X) : ℝ :=
  comparisonAngle T.p₁ T.p₂ T.p₃

def GeodesicTriangle.comparisonAngleAt₂ {X : Type*} [MetricSpace X]
    (T : GeodesicTriangle X) : ℝ :=
  comparisonAngle T.p₂ T.p₁ T.p₃

def GeodesicTriangle.comparisonAngleAt₃ {X : Type*} [MetricSpace X]
    (T : GeodesicTriangle X) : ℝ :=
  comparisonAngle T.p₃ T.p₁ T.p₂

end Geodesics
end
