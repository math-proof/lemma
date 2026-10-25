/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2322.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Theorem.v1.Atlas.NumberTheoryI.code.Cor2322
universe u


instance chainsFunctor_additive (k G : Type u) [CommRing k] [Group G] :
    (groupHomology.chainsFunctor k G).Additive where
  map_add {X Y f g} := by
    ext n : 1
    show (groupHomology.chainsMap (MonoidHom.id G) (f + g)).f n =
      ((groupHomology.chainsMap (MonoidHom.id G) f) +
        (groupHomology.chainsMap (MonoidHom.id G) g)).f n
    have key : ∀ (φ : X ⟶ Y), (groupHomology.chainsMap (MonoidHom.id G) φ).f n =
      ModuleCat.ofHom (Finsupp.mapRange.linearMap (Rep.Hom.hom φ).toLinearMap ∘ₗ
        Finsupp.lmapDomain (↑X) k fun x => (MonoidHom.id G) ∘ x) := fun φ =>
      groupHomology.chainsMap_f (MonoidHom.id G) φ n
    rw [key (f + g)]
    conv_rhs =>
      rw [show (groupHomology.chainsMap (MonoidHom.id G) f +
        groupHomology.chainsMap (MonoidHom.id G) g).f n =
        (groupHomology.chainsMap (MonoidHom.id G) f).f n +
        (groupHomology.chainsMap (MonoidHom.id G) g).f n from rfl, key f, key g]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    show ((Finsupp.mapRange.linearMap (Rep.Hom.hom (f + g)).toLinearMap ∘ₗ
        Finsupp.lmapDomain (↑X) k fun σ => (MonoidHom.id G) ∘ σ) x) =
      ((Finsupp.mapRange.linearMap (Rep.Hom.hom f).toLinearMap ∘ₗ
        Finsupp.lmapDomain (↑X) k fun σ => (MonoidHom.id G) ∘ σ) x) +
      ((Finsupp.mapRange.linearMap (Rep.Hom.hom g).toLinearMap ∘ₗ
        Finsupp.lmapDomain (↑X) k fun σ => (MonoidHom.id G) ∘ σ) x)
    simp only [LinearMap.comp_apply]
    rw [show (Rep.Hom.hom (f + g)).toLinearMap =
      (Rep.Hom.hom f).toLinearMap + (Rep.Hom.hom g).toLinearMap from rfl]
    exact mapRange_linearMap_add_apply _ _ _

