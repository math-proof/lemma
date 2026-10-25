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
import Def.v1.Atlas.DifferentialGeometry.code.GeodesicTriangles
open scoped InnerProductSpace
open EuclideanGeometry


noncomputable section

namespace Geodesics

structure ComparisonTriangle (X : Type*) [MetricSpace X] (T : GeodesicTriangle X) where
  q₁ : EuclideanSpace ℝ (Fin 2)
  q₂ : EuclideanSpace ℝ (Fin 2)
  q₃ : EuclideanSpace ℝ (Fin 2)
  dist_eq₁₂ : dist q₁ q₂ = dist T.p₁ T.p₂
  dist_eq₂₃ : dist q₂ q₃ = dist T.p₂ T.p₃
  dist_eq₁₃ : dist q₁ q₃ = dist T.p₁ T.p₃

end Geodesics
end
