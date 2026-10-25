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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section10
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology

noncomputable section

variable (X : Type) [TopologicalSpace X] (A U : Set X)

/-- The chain map between relative chain complexes
`C_*(X ∖ U, A ∖ U) → C_*(X, A)` induced by the pair inclusion. Excision asserts that this
map is a quasi-isomorphism whenever `(X, A, U)` is excisive. -/
def excisionRelativeChainMap :
    relativeSingularChainComplex (Uᶜ : Set X) (Subtype.val ⁻¹' A) ⟶
    relativeSingularChainComplex X A :=
  cokernel.map _ _
    (singularChainZ.map (excisedSubsetToSubspace X A U))
    (singularChainZ.map (complementInclusion X U))
    (by
      show singularChainZ.map _ ≫ singularChainZ.map _ =
        singularChainZ.map _ ≫ singularChainZ.map _
      rw [← singularChainZ.map_comp, ← singularChainZ.map_comp, excision_square_comm])

/-- The induced map on degree-`n` relative homology
`H_n(X ∖ U, A ∖ U) → H_n(X, A)` coming from the excision chain map. -/
def excisionHomologyMap (n : ℕ) :
    RelativeSingularHomologyGroup n (Uᶜ : Set X) (Subtype.val ⁻¹' A) ⟶
    RelativeSingularHomologyGroup n X A :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).map
    (excisionRelativeChainMap X A U)

end

end Excision

namespace Excision

open AlgebraicTopology Set

noncomputable section

/-- The *small chain complex* `C^{\{A, B\}}_*(X)` for the two-element cover `{A, B}`: the
image of the chain map `C_*(A) ⊕ C_*(B) → C_*(X)` sending a pair to the sum of its
components in `C_*(X)`. -/
def smallChainComplex (X : Type) [TopologicalSpace X] (A B : Set X) :
    ChainComplex AddCommGrpCat ℕ :=
  image (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B))

/-- The inclusion `C^{\{A, B\}}_*(X) ↪ C_*(X)` of the small chain complex into the full
singular chain complex (the canonical image inclusion). -/
def smallChainInclusion (X : Type) [TopologicalSpace X] (A B : Set X) :
    smallChainComplex X A B ⟶ singularChainZ.obj (TopCat.of X) :=
  image.ι _


end
end Excision
