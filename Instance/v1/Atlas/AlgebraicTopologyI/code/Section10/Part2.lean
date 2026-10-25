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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section10.Part3
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology Set

noncomputable section

/-- The total singular simplicial set functor `TopCat ⥤ SSet` preserves monomorphisms: an
injective continuous map is sent to a degreewise-injective map of simplicial sets. -/
instance toSSet_preservesMono : TopCat.toSSet.{0}.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    rw [NatTrans.mono_iff_mono_app]
    intro n; rw [mono_iff_injective]
    intro σ₁ σ₂ h
    simp only [TopCat.toSSet, Presheaf.restrictedULiftYoneda, Functor.comp_map,
      Functor.whiskeringLeft, uliftYoneda] at h
    dsimp [Functor.whiskerLeft, yoneda, uliftFunctor] at h
    have h' : σ₁.down ≫ f = σ₂.down ≫ f := by
      have := congr_arg ULift.down h; simp at this; exact this
    exact ULift.ext _ _ ((cancel_mono f).mp h')

/-- The singular chain functor `C_*(-; ℤ) : TopCat ⥤ ChainComplex AddCommGrp` preserves
monomorphisms. -/
instance singularChainZ_preservesMono : singularChainZ.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    apply HomologicalComplex.mono_of_mono_f
    intro i
    change Mono ((sigmaConst.obj (AddCommGrpCat.of ℤ)).map
      ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk i))))
    apply sigmaConst_map_mono_of_injective
    haveI : Mono (TopCat.toSSet.map f) := Functor.map_mono TopCat.toSSet f
    have hmono_app : Mono ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk i))) :=
      (NatTrans.mono_iff_mono_app (TopCat.toSSet.map f)).mp this _
    exact (mono_iff_injective _).mp hmono_app


/-- The chain inclusion `C_*(A) ↪ C_*(X)` induced by `A ↪ X` is a monomorphism. -/
instance subspaceChainInclusion_mono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (subspaceChainInclusion X A) := by
  unfold subspaceChainInclusion
  haveI : Mono (subspaceTopInclusion A) := by
    rw [TopCat.mono_iff_injective]; exact Subtype.val_injective
  exact Functor.map_mono singularChainZ (subspaceTopInclusion A)

attribute [instance] subspaceChainInclusion_mono

/-- The map `C_*(A) → C^{\{A, B\}}_*(X)` is a monomorphism. -/
instance smallChainInclusionA_mono (X : Type) [TopologicalSpace X] (A B : Set X) :
    Mono (smallChainInclusionA X A B) :=
  mono_of_mono_fac (smallChainInclusionA_comp_ι X A B)

/-- The first map in `topSES X A B` is a monomorphism. -/
instance topSES_mono_f (X : Type) [TopologicalSpace X] (A B : Set X) :
    Mono (topSES X A B).f := smallChainInclusionA_mono X A B

/-- The second map in `topSES X A B` is an epimorphism (as a cokernel projection). -/
instance topSES_epi_g (X : Type) [TopologicalSpace X] (A B : Set X) :
    Epi (topSES X A B).g := by
  show Epi (cokernel.π (smallChainInclusionA X A B))
  infer_instance

/-- The first map in `bottomSES X A` is a monomorphism. -/
instance bottomSES_mono_f (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (bottomSES X A).f := subspaceChainInclusion_mono X A

/-- The second map in `bottomSES X A` is an epimorphism (as a cokernel projection). -/
instance bottomSES_epi_g (X : Type) [TopologicalSpace X] (A : Set X) :
    Epi (bottomSES X A).g := by
  show Epi (cokernel.π (subspaceChainInclusion X A))
  infer_instance

end
end Excision
