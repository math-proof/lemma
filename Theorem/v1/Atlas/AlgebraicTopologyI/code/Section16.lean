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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section16
open AlgebraicTopology CategoryTheory Limits AlgebraicTopologyI


noncomputable section

namespace CWComplex.SkeletonHomology

/-- Commutativity of the natural square for the pair maps: the subspace inclusion of
`X_k` (as a preimage in `X_m`) into `X_m`, then into `X`, equals the composition through
`X_k ⊆ X`. -/
lemma CWComplex.SkeletonHomology.skelPairSquare_comm
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (k m : ℕ) :
    Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) ≫
    CWComplex.SkeletonHomology.skeletonInclusion X m =
    CWComplex.SkeletonHomology.skelPairSubspaceMap k m ≫
    Excision.subspaceTopInclusion (↑(CWComplex.skeleton X k : Set X) : Set X) := by
  ext ⟨⟨_, _⟩, _⟩; rfl

end CWComplex.SkeletonHomology
end
