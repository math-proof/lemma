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
public import Def.v1.Atlas.DifferentialGeometry.code.GaussBonnet.Part4
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

attribute [instance] Triangulation.finVertex

attribute [instance] Triangulation.finEdge

attribute [instance] Triangulation.finFace

attribute [instance] Triangulation.decVertex

attribute [instance] Triangulation.decEdge

attribute [instance] Triangulation.decFace

variable {M : Set (Fin 3 → ℝ)} (τ : Triangulation M)

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

end CombinatorialGaussBonnet
