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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part11
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace SphereHomology

open AlgebraicTopology

noncomputable section

/-- The topological inclusion `A ↪ X` is a monomorphism in `TopCat`. -/
instance inclTopMono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (TopCat.ofHom (⟨(Subtype.val : A → X), continuous_subtype_val⟩ : C(A, X))) := by
  rw [TopCat.mono_iff_injective]; exact Subtype.val_injective


/-- The chain-level inclusion `inclChain` is a monomorphism. -/
instance inclChainMono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (inclChain X A) := by
  haveI := singularChainZ_preserves_mono
  exact Functor.PreservesMonomorphisms.preserves _


end
end SphereHomology
