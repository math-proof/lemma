module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section31
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part7
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Order.Directed
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.Sets.Opens
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section34.Part5
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section34.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace CechCohomology

/-- The preorder on `OpenCover Y` where `𝒰 ≤ 𝒱` iff `𝒱` refines `𝒰`.
Reflexivity is the trivial self-refinement; transitivity composes
witnesses. -/
instance openCoverPreorder {Y : Type} [TopologicalSpace Y] :
    Preorder (OpenCover Y) where
  le 𝒰 𝒱 := 𝒱.Refines 𝒰
  le_refl 𝒰 := fun V hV => ⟨V, hV, le_refl _⟩
  le_trans _ _ _ h1 h2 := by
    intro W hW
    obtain ⟨V, hV, hWV⟩ := h2 W hW
    obtain ⟨U, hU, hVU⟩ := h1 V hV
    exact ⟨U, hU, hWV.trans hVU⟩

end CechCohomology
end
