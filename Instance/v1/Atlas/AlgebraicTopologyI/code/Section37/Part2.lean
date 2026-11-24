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
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section37.Part2
open CategoryTheory
open CategoryTheory TopologicalSpace Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section37.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace PoincareDuality

universe u

section OpenNhdsColimit

variable {α : Type u} [TopologicalSpace α]

namespace CombinedOpenNhds

variable {A : ℕ → Set α}

/-- Reverse-inclusion preorder on `CombinedOpenNhds`: $(k, U) \le (k', V)$ iff
$V \subseteq U$, ignoring the indices. -/
instance : Preorder (CombinedOpenNhds A) where
  le p q := q.nhd.toOpens ≤ p.nhd.toOpens
  le_refl _ := le_refl _
  le_trans _ _ _ hab hbc := le_trans hbc hab

/-- The pair $(0, \top)$ is always a combined open neighbourhood, hence the type is
nonempty. -/
instance : Nonempty (CombinedOpenNhds A) := ⟨⟨0, ⟨⊤, Set.subset_univ _⟩⟩⟩

end CombinedOpenNhds
end OpenNhdsColimit
end PoincareDuality
