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
public section

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

end CombinatorialGaussBonnet
