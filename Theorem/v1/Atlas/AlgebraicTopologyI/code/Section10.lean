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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part2
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology

noncomputable section

variable (X : Type) [TopologicalSpace X] (A U : Set X)

/-- Commutativity of the square `(A ∖ U) ↪ (X ∖ U); (A ∖ U) ↪ A` with `(X ∖ U) ↪ X; A ↪ X`,
which is what makes the excision pair-inclusion a well-defined morphism of pairs. -/
lemma excision_square_comm :
    subspaceTopInclusion (Subtype.val ⁻¹' A : Set (Uᶜ : Set X)) ≫
      complementInclusion X U =
    excisedSubsetToSubspace X A U ≫ subspaceTopInclusion A := by
  ext ⟨⟨_, _⟩, _⟩; rfl

end
end Excision
