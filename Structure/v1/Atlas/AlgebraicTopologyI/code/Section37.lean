/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section37.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Comma.Final
public import Mathlib.Topology.Separation.Hausdorff
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section37
public section

open CategoryTheory

open CategoryTheory TopologicalSpace Limits


namespace PoincareDuality

universe u

section OpenNhdsColimit

variable {α : Type u} [TopologicalSpace α]

/-- An open neighbourhood of a set $K$: an open subset $U \subseteq \alpha$ together with
the inclusion $K \subseteq U$. The indexing category for the Čech-cohomology colimit. -/
structure OpenNhdsOfSet (K : Set α) where
  toOpens : Opens α
  subset_carrier : K ⊆ toOpens.carrier

end OpenNhdsColimit
end PoincareDuality
