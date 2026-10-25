/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section34.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section31
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part7
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Order.Directed
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Sets.Opens
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Def.v1.Atlas.AlgebraicTopologyI.code.Section34.Part2
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


noncomputable section

namespace CechCohomology

/-- The reverse-inclusion preorder on open neighborhoods of `K`: `U ≤ V`
means `V ⊆ U`.  This is the standard convention so that "smaller
neighborhoods" come later, making the system *directed downward* and
inducing the correct directed colimit on cohomology. -/
instance openNeighborhoods_preorder {X : Type*} [TopologicalSpace X] (K : Set X) :
    Preorder (OpenNeighborhoods K) where
  le U V := V.1 ≤ U.1
  le_refl _ := le_refl _
  le_trans _ _ _ h1 h2 := le_trans h2 h1

/-- The poset of open neighborhoods of `K` is directed: any two
neighborhoods `U` and `V` are both refined by their intersection `U ∩ V`,
which is again open and still contains `K`. -/
instance openNeighborhoods_directed {X : Type*} [TopologicalSpace X] (K : Set X) :
    IsDirected (OpenNeighborhoods K) (· ≤ ·) where
  directed U V := by
    refine ⟨⟨U.1 ⊓ V.1, ?_⟩, ?_, ?_⟩
    · intro x hx; exact ⟨U.2 hx, V.2 hx⟩
    · show U.1 ⊓ V.1 ≤ U.1; exact inf_le_left
    · show U.1 ⊓ V.1 ≤ V.1; exact inf_le_right

/-- The poset of open neighborhoods of `K` is nonempty: the ambient space
`X = ⊤` is always an open neighborhood of `K`. -/
instance openNeighborhoods_nonempty {X : Type*} [TopologicalSpace X] (K : Set X) :
    Nonempty (OpenNeighborhoods K) :=
  ⟨⟨⊤, fun _ _ => trivial⟩⟩

end CechCohomology
end
