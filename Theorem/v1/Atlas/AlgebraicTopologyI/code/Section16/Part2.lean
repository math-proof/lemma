/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section15
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section15
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Algebra.Category.Grp.Abelian
import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part3
open AlgebraicTopology CategoryTheory Limits AlgebraicTopologyI


noncomputable section

namespace CWComplex.SkeletonHomology

namespace CWHomology

/-- The naturality square between the inclusion of the previous-skeleton subspace into
the `n`-skeleton, and the cellular map restricted to skeletons, commutes. -/
lemma cellularMapSquare_comm
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X) :
      Set ↥(CWComplex.skeleton X (n : ℕ∞) : Set X)) ≫
    cellularMapOnSkeleton f hf n =
    cellularMapOnPrevSkeleton f hf n ≫
    Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton Y ((↑(n - 1) : ℕ∞)) : Set Y) :
      Set ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y)) := by
  ext ⟨⟨_, _⟩, _⟩; rfl

end CWHomology
end CWComplex.SkeletonHomology
end
