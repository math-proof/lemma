/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussBonnet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Def.v1.Atlas.DifferentialGeometry.code.GaussMapDegree.Part4
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.GaussMapDegree
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
public import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
public import Def.v1.Atlas.DifferentialGeometry.code.GaussBonnet.Part2
public section

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

end CombinatorialGaussBonnet
