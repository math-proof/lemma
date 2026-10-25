/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussBonnet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.LinearCombination
import Def.v1.Atlas.DifferentialGeometry.code.GaussMapDegree.Part4
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.GaussMapDegree
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
import Def.v1.Atlas.DifferentialGeometry.code.GaussBonnet.Part3
open Finset Real


namespace CombinatorialGaussBonnet

attribute [instance] CompactCombinatorialSurface.finVertex

attribute [instance] CompactCombinatorialSurface.finEdge

attribute [instance] CompactCombinatorialSurface.decEdge

variable (S : CompactCombinatorialSurface)

attribute [instance] SurfaceTriangulation.finV

attribute [instance] SurfaceTriangulation.finE

attribute [instance] SurfaceTriangulation.finF

attribute [instance] SurfaceTriangulation.decV

attribute [instance] SurfaceTriangulation.decF

variable (T : SurfaceTriangulation)

attribute [instance] Triangulation.finVertex

attribute [instance] Triangulation.finEdge

attribute [instance] Triangulation.finFace

attribute [instance] Triangulation.decVertex

attribute [instance] Triangulation.decEdge

attribute [instance] Triangulation.decFace

variable {M : Set (Fin 3 → ℝ)} (τ : Triangulation M)

structure MovingFrameWithSingularities
    (M : Set (EuclideanSpace ℝ (Fin 3))) where
  singularPoints : Finset (EuclideanSpace ℝ (Fin 3))
  sing_in_M : ∀ p ∈ singularPoints, p ∈ M
  frame₁ : ↥(M \ ↑singularPoints) → EuclideanSpace ℝ (Fin 3)
  frame₂ : ↥(M \ ↑singularPoints) → EuclideanSpace ℝ (Fin 3)
  surfaceNormal : ↥(M \ ↑singularPoints) → EuclideanSpace ℝ (Fin 3)
  frame₁_unit : ∀ y : ↥(M \ ↑singularPoints), ‖frame₁ y‖ = 1
  frame₂_unit : ∀ y : ↥(M \ ↑singularPoints), ‖frame₂ y‖ = 1
  normal_unit : ∀ y : ↥(M \ ↑singularPoints), ‖surfaceNormal y‖ = 1
  frame_orthogonal : ∀ y : ↥(M \ ↑singularPoints),
    inner (𝕜 := ℝ) (frame₁ y) (frame₂ y) = 0
  frame₁_tangent : ∀ y : ↥(M \ ↑singularPoints),
    inner (𝕜 := ℝ) (frame₁ y) (surfaceNormal y) = 0
  frame₂_tangent : ∀ y : ↥(M \ ↑singularPoints),
    inner (𝕜 := ℝ) (frame₂ y) (surfaceNormal y) = 0
  frame_pos_oriented : ∀ y : ↥(M \ ↑singularPoints),
    0 < Matrix.det (Matrix.of fun (i j : Fin 3) =>
      (![frame₁ y, frame₂ y, surfaceNormal y] : Fin 3 → EuclideanSpace ℝ (Fin 3)) j i)
  multiplicity : ↥singularPoints → ℤ

structure CompactSurface where
  carrier : Set (Fin 3 → ℝ)
  carrier_smooth : GaussMapDegree.IsSmHypersurface 2 carrier
  carrier_compact : IsCompact carrier
  carrier_nonempty : carrier.Nonempty
  gaussMap : (Fin 3 → ℝ) → (Fin 3 → ℝ)
  gaussMap_maps_to_sphere : ∀ p ∈ carrier, ‖gaussMap p‖ = 1
  gaussianCurvature : (Fin 3 → ℝ) → ℝ
  localParam : (Fin 2 → ℝ) → Fin 3 → ℝ
  localParamInv : (Fin 3 → ℝ) → Fin 2 → ℝ
  gaussianCurvature_eq : ∀ p ∈ carrier,
    gaussianCurvature p = GaussMapDegree.jacobianDetAtPoint gaussMap
      localParam (localParamInv p) (gaussMap p)
  gaussMapDegree : ℤ
  gaussMapDegree_eq :
    (∫ p in carrier, gaussianCurvature p ∂(MeasureTheory.Measure.hausdorffMeasure (2 : ℝ))) =
      (gaussMapDegree : ℝ) * (4 * Real.pi)
  triangulation : SurfaceTriangulation
  vertexPos : triangulation.V → (Fin 3 → ℝ)
  vertices_in_carrier : ∀ v, vertexPos v ∈ carrier

end CombinatorialGaussBonnet
