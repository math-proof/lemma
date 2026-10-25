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
open scoped InnerProductSpace
open EuclideanGeometry


noncomputable section

namespace Geodesics

structure IsMetricGeodesicSegment {X : Type*} [MetricSpace X] (γ : ℝ → X)
    (p q : X) : Prop where
  source : γ 0 = p
  target : γ 1 = q
  proportional : ∀ s t : ℝ, s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
    dist (γ s) (γ t) = |t - s| * dist p q

structure GeodesicTriangle (X : Type*) [MetricSpace X] where
  p₁ : X
  p₂ : X
  p₃ : X
  γ₁₂ : ℝ → X
  γ₂₃ : ℝ → X
  γ₁₃ : ℝ → X
  isGeodesic₁₂ : IsMetricGeodesicSegment γ₁₂ p₁ p₂
  isGeodesic₂₃ : IsMetricGeodesicSegment γ₂₃ p₂ p₃
  isGeodesic₁₃ : IsMetricGeodesicSegment γ₁₃ p₁ p₃

end Geodesics
end
