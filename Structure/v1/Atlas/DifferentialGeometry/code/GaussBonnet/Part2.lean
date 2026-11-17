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
public import Def.v1.Atlas.DifferentialGeometry.code.GaussBonnet
public section

open Finset Real


namespace CombinatorialGaussBonnet

attribute [instance] CompactCombinatorialSurface.finVertex

attribute [instance] CompactCombinatorialSurface.finEdge

attribute [instance] CompactCombinatorialSurface.decEdge

variable (S : CompactCombinatorialSurface)

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

end CombinatorialGaussBonnet
