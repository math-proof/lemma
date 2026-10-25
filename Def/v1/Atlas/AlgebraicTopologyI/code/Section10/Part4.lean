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
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section10
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology Set

noncomputable section

/-- The canonical strong epimorphism `C_*(A) ⊕ C_*(B) ↠ C^{\{A, B\}}_*(X)` from the
biproduct to the small singular chain complex for the two-element cover `{A, B}`. -/
def smallChainInclusionA (X : Type) [TopologicalSpace X] (A B : Set X) :
    singularChainZ.obj (TopCat.of A) ⟶ smallChainComplex X A B :=
  biprod.inl ≫ factorThruImage (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B))

end
end Excision
