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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section10.Part7
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace SphereHomology

open AlgebraicTopology

noncomputable section

/-- Local copy of `toSSet_preservesMono` in the `SphereHomology` namespace. -/
instance toSSet_preservesMono' : TopCat.toSSet.{0}.PreservesMonomorphisms where
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

/-- The `singularChainZF` functor preserves monomorphisms. -/
instance singularChainZ_preserves_mono : singularChainZF.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    apply HomologicalComplex.mono_of_mono_f
    intro i
    change Mono ((sigmaConst.obj (AddCommGrpCat.of ℤ)).map
      ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk i))))
    apply sigmaConst_map_mono_of_injective'
    haveI : Mono (TopCat.toSSet.map f) := Functor.map_mono TopCat.toSSet f
    have hmono_app : Mono ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk i))) :=
      (NatTrans.mono_iff_mono_app (TopCat.toSSet.map f)).mp this _
    exact (mono_iff_injective _).mp hmono_app


end
end SphereHomology
