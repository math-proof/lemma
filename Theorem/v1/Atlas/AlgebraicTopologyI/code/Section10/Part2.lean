/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part4
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology Set

noncomputable section

/-- Compatibility: the small-complex factorization of `C_*(A) ↪ C_*(X)` composed with the
inclusion of the small complex into `C_*(X)` recovers the original inclusion. -/
lemma smallChainInclusionA_comp_ι (X : Type) [TopologicalSpace X] (A B : Set X) :
    smallChainInclusionA X A B ≫ smallChainInclusion X A B =
    subspaceChainInclusion X A := by
  change (biprod.inl ≫ factorThruImage
    (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B))) ≫
    image.ι (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B)) = _
  rw [Category.assoc, image.fac, biprod.inl_desc]

end
end Excision
