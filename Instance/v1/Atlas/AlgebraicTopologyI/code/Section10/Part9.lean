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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part14
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace SphereHomology

open AlgebraicTopology

section SuspensionIsoProof

open AlgebraicTopology

noncomputable section

/-- Local copy of `inclTopMono` for the suspension-isomorphism proof. -/
instance suspInclTopMono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (TopCat.ofHom (⟨(Subtype.val : A → X), continuous_subtype_val⟩ : C(A, X))) := by
  rw [TopCat.mono_iff_injective]; exact Subtype.val_injective

/-- Local copy of `inclChainMono` for the suspension-isomorphism proof. -/
instance suspInclChainMono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (suspInclChain X A) := by
  haveI := suspSingularChainZ_preserves_mono
  exact Functor.PreservesMonomorphisms.preserves _

end
end SuspensionIsoProof
end SphereHomology
