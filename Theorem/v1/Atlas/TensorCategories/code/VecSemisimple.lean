/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecSemisimple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
import Lemma.Category.Atlas.v1.TensorCategories.code.VecInstances
import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2
import Instance.v1.Atlas.TensorCategories.code.VecSemisimple
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Module

universe u


noncomputable section

namespace VecSemisimple

variable (k : Type u) [Field k]

/-- An object `X` of `FGModuleCat k` that is not categorically zero is nontrivial
as a vector space, i.e. it contains a nonzero element. -/
lemma nontrivial_of_not_isZero (X : FGModuleCat.{u} k) (h : ¬ IsZero X) :
    Nontrivial X := by
  rw [IsZero.iff_id_eq_zero] at h
  by_contra hnt; apply h
  simp only [not_nontrivial_iff_subsingleton] at hnt
  ext x
  have : x = (0 : X) := @Subsingleton.elim _ hnt x 0
  subst this; rfl

/-- The morphism `k ⟶ X` sending `1` to a nonzero vector `v ∈ X` is itself nonzero
in `FGModuleCat k`. -/
lemma ofHom_toSpanSingleton_ne_zero (X : FGModuleCat.{u} k) (v : X) (hv : v ≠ 0) :
    FGModuleCat.ofHom (LinearMap.toSpanSingleton k (↑X) v) ≠
      (0 : FGModuleCat.of k k ⟶ X) := by
  intro h; apply hv
  have key : LinearMap.toSpanSingleton k (↑X) v = (0 : k →ₗ[k] X) := by
    have := congr_arg (fun f => f.hom.hom) h
    simpa using this
  have := congr_fun (congr_arg DFunLike.coe key) (1 : k)
  simpa [LinearMap.toSpanSingleton_apply] using this

/-- The morphism `k ⟶ X` sending `1` to a nonzero vector `v ∈ X` is a monomorphism
in `FGModuleCat k`, since `c ↦ c • v` is injective when `v ≠ 0`. -/
lemma mono_ofHom_toSpanSingleton (X : FGModuleCat.{u} k) (v : X) (hv : v ≠ 0) :
    Mono (FGModuleCat.ofHom (LinearMap.toSpanSingleton k (↑X) v) :
      FGModuleCat.of k k ⟶ X) := by
  apply (forget₂ (FGModuleCat k) (ModuleCat k)).mono_of_mono_map
  rw [ModuleCat.mono_iff_injective]
  show Function.Injective (LinearMap.toSpanSingleton k (↑X) v)
  intro a b hab
  simp [LinearMap.toSpanSingleton_apply] at hab
  have h : (a - b) • v = 0 := by rw [sub_smul, hab, sub_self]
  rcases smul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv

end VecSemisimple
end
