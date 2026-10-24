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
import sympy.atlas.v1.Atlas.DifferentialGeometry.code.GaussMapDegree
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.GaussMapDegree
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
import sympy.atlas.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
open Finset Real

namespace CombinatorialGaussBonnet

structure CompactCombinatorialSurface where
  numPolygons : ℕ
  polygon : Fin numPolygons → Set (Fin 3 → ℝ)
  polygon_convex : ∀ i, Convex ℝ (polygon i)
  polygon_flat : ∀ i, ∃ (p : Fin 3 → ℝ) (n : Fin 3 → ℝ), n ≠ 0 ∧
    ∀ x ∈ polygon i, ∑ k, (x k - p k) * n k = (0 : ℝ)
  Vertex : Type
  [finVertex : Fintype Vertex]
  vertexPos : Vertex → (Fin 3 → ℝ)
  Edge : Type
  [finEdge : Fintype Edge]
  [decEdge : DecidableEq Edge]
  edgeSet : Edge → Set (Fin 3 → ℝ)
  edgesOf : Fin numPolygons → Finset Edge
  edge_subset : ∀ i, ∀ e ∈ edgesOf i, edgeSet e ⊆ polygon i
  disjoint_or_common_edge : ∀ i j, i ≠ j →
    Disjoint (polygon i) (polygon j) ∨
    ∃ e : Edge, e ∈ edgesOf i ∧ e ∈ edgesOf j
  edge_exactly_two : ∀ i, ∀ e ∈ edgesOf i,
    ∃! j, j ≠ i ∧ e ∈ edgesOf j

attribute [instance] CompactCombinatorialSurface.finVertex
attribute [instance] CompactCombinatorialSurface.finEdge
attribute [instance] CompactCombinatorialSurface.decEdge

variable (S : CompactCombinatorialSurface)

noncomputable def CompactCombinatorialSurface.numVertices : ℕ :=
  Fintype.card S.Vertex

noncomputable def CompactCombinatorialSurface.numEdges : ℕ :=
  Fintype.card S.Edge

noncomputable def CompactCombinatorialSurface.eulerCharacteristic : ℤ :=
  (S.numVertices : ℤ) - (S.numEdges : ℤ) + (S.numPolygons : ℤ)

structure SurfaceTriangulation where
  V : Type
  E : Type
  F : Type
  [finV : Fintype V]
  [finE : Fintype E]
  [finF : Fintype F]
  [decV : DecidableEq V]
  [decF : DecidableEq F]
  facesAt : V → Finset F
  angleAt : V → F → ℝ
  verticesOf : F → Finset V
  face_card : ∀ f : F, (verticesOf f).card = 3
  mem_facesAt_iff : ∀ v f, f ∈ facesAt v ↔ v ∈ verticesOf f
  angle_sum_face : ∀ f : F, (verticesOf f).sum (fun v => angleAt v f) = π
  two_edges_eq_three_faces : 2 * Fintype.card E = 3 * Fintype.card F

attribute [instance] SurfaceTriangulation.finV
attribute [instance] SurfaceTriangulation.finE
attribute [instance] SurfaceTriangulation.finF
attribute [instance] SurfaceTriangulation.decV
attribute [instance] SurfaceTriangulation.decF

variable (T : SurfaceTriangulation)

noncomputable def SurfaceTriangulation.numVertices : ℕ := Fintype.card T.V

noncomputable def SurfaceTriangulation.numEdges : ℕ := Fintype.card T.E

noncomputable def SurfaceTriangulation.numFaces : ℕ := Fintype.card T.F

noncomputable def SurfaceTriangulation.eulerCharacteristic : ℤ :=
  (T.numVertices : ℤ) - (T.numEdges : ℤ) + (T.numFaces : ℤ)

noncomputable def SurfaceTriangulation.gaussCurvatureComb (v : T.V) : ℝ :=
  2 * π - (T.facesAt v).sum (T.angleAt v)

structure Triangulation (M : Set (Fin 3 → ℝ)) where
  Vertex : Type
  [finVertex : Fintype Vertex]
  [decVertex : DecidableEq Vertex]
  Edge : Type
  [finEdge : Fintype Edge]
  [decEdge : DecidableEq Edge]
  Face : Type
  [finFace : Fintype Face]
  [decFace : DecidableEq Face]
  vertexPos : Vertex → (Fin 3 → ℝ)
  vertex_mem : ∀ v, vertexPos v ∈ M
  faceRegion : Face → Set (Fin 3 → ℝ)
  face_subset : ∀ f, faceRegion f ⊆ M
  covering : ∀ p ∈ M, ∃ f, p ∈ faceRegion f
  faceVertices : Face → Fin 3 → Vertex
  faceVertices_injective : ∀ f, Function.Injective (faceVertices f)
  edgeEndpoints : Edge → Fin 2 → Vertex
  edgeEndpoints_injective : ∀ e, Function.Injective (edgeEndpoints e)
  faceEdges : Face → Fin 3 → Edge
  edge_shared_by_two : ∀ e : Edge,
    ∃ f₁ f₂ : Face, f₁ ≠ f₂ ∧
      (∀ f : Face, e ∈ Set.range (faceEdges f) → f = f₁ ∨ f = f₂)
  intersection_regularity : ∀ f₁ f₂ : Face, f₁ ≠ f₂ →
    (faceRegion f₁ ∩ faceRegion f₂ = ∅) ∨
    (∃ v : Vertex, faceRegion f₁ ∩ faceRegion f₂ = {vertexPos v}) ∨
    (∃ e : Edge, e ∈ Set.range (faceEdges f₁) ∧ e ∈ Set.range (faceEdges f₂))

attribute [instance] Triangulation.finVertex
attribute [instance] Triangulation.finEdge
attribute [instance] Triangulation.finFace
attribute [instance] Triangulation.decVertex
attribute [instance] Triangulation.decEdge
attribute [instance] Triangulation.decFace

variable {M : Set (Fin 3 → ℝ)} (τ : Triangulation M)

noncomputable def Triangulation.numVertices : ℕ := Fintype.card τ.Vertex

noncomputable def Triangulation.numEdges : ℕ := Fintype.card τ.Edge

noncomputable def Triangulation.numFaces : ℕ := Fintype.card τ.Face

noncomputable def Triangulation.eulerCharacteristic : ℤ :=
  (τ.numVertices : ℤ) - (τ.numEdges : ℤ) + (τ.numFaces : ℤ)

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

noncomputable def CompactSurface.eulerCharacteristic (M : CompactSurface) : ℤ :=
  M.triangulation.eulerCharacteristic

noncomputable def CompactSurface.totalGaussianCurvature (M : CompactSurface) : ℝ :=
  ∫ p in M.carrier, M.gaussianCurvature p ∂(MeasureTheory.Measure.hausdorffMeasure (2 : ℝ))

structure CompactSurface where
  M : Set (Fin 3 → ℝ)
  M_compact : IsCompact M
  M_connected : IsConnected M
  M_nonempty : M.Nonempty
  gaussMap : (Fin 3 → ℝ) → (Fin 3 → ℝ)
  gaussMap_smooth : ContDiffOn ℝ ⊤ gaussMap M
  gaussMap_maps_to_sphere : ∀ p ∈ M, ‖gaussMap p‖ = 1
  gaussianCurvature : (Fin 3 → ℝ) → ℝ
  localParam : (Fin 2 → ℝ) → Fin 3 → ℝ
  localParamInv : (Fin 3 → ℝ) → Fin 2 → ℝ
  gaussianCurvature_eq : ∀ p ∈ M,
    gaussianCurvature p = GaussMapDegree.jacobianDetAtPoint gaussMap
      localParam (localParamInv p) (gaussMap p)
  gaussMapDegree : ℤ
  gaussMap_degree_ge_one : (1 : ℤ) ≤ |gaussMapDegree|

noncomputable def CompactSurface.totalAbsCurvature (S : CompactSurface) : ℝ :=
  ∫ p in S.M, |S.gaussianCurvature p| ∂(Measure.hausdorffMeasure (2 : ℝ))


end CompactSurfaceCurvature

namespace GaussBonnetBoundary

open Real MeasureTheory

structure DiscRegion where
  surface : Set (Fin 3 → ℝ)
  region : Set (Fin 3 → ℝ)
  region_subset : region ⊆ surface
  region_connected : IsPathConnected region
  numCorners : ℕ
  gaussianCurvature : (Fin 3 → ℝ) → ℝ
  patch : HypersurfacePatch 2
  paramDomain : Set (Fin 2 → ℝ)
  paramDomain_sub : paramDomain ⊆ patch.domain
  region_eq : region = patch.f '' paramDomain
  curvature_consistent : ∀ x ∈ paramDomain,
    gaussianCurvature (patch.f x) = gaussCurvature patch x
  totalGaussianCurvature : ℝ
  totalCurvature_eq : totalGaussianCurvature =
    ∫ x in paramDomain, gaussCurvature patch x *
      Real.sqrt (firstFundamentalForm patch x).det
  totalGeodesicCurvature : ℝ
  exteriorAngles : Fin numCorners → ℝ

variable (D : DiscRegion)

noncomputable def DiscRegion.sumExteriorAngles : ℝ :=
  ∑ i : Fin D.numCorners, D.exteriorAngles i


structure GeodesicTriangleRegion extends DiscRegion where
  corners_eq : toDiscRegion.numCorners = 3
  angle₁ : ℝ
  angle₂ : ℝ
  angle₃ : ℝ
  geodesic_boundary : toDiscRegion.totalGeodesicCurvature = 0
  ext_angle_0 : toDiscRegion.exteriorAngles (Fin.cast corners_eq.symm 0) = π - angle₁
  ext_angle_1 : toDiscRegion.exteriorAngles (Fin.cast corners_eq.symm 1) = π - angle₂
  ext_angle_2 : toDiscRegion.exteriorAngles (Fin.cast corners_eq.symm 2) = π - angle₃
