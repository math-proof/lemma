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
import Theorem.v1.Atlas.TensorCategories.code.VecSemisimple
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Module

universe u


noncomputable section

namespace VecSemisimple

variable (k : Type u) [Field k]

/-- Every simple object `X` in `FGModuleCat k` is isomorphic to the ground field `k`,
since a nonzero vector spans a one-dimensional subspace which then forces an iso. -/
def simple_iso_of_k (X : FGModuleCat.{u} k) [Simple X] :
    X ≅ FGModuleCat.of k k := by
  haveI hnt : Nontrivial X := nontrivial_of_not_isZero k X (Simple.not_isZero X)
  let v : X := (exists_ne (0 : X)).choose
  have hv : v ≠ 0 := (exists_ne (0 : X)).choose_spec
  let f : FGModuleCat.of k k ⟶ X :=
    FGModuleCat.ofHom (LinearMap.toSpanSingleton k (↑X) v)
  have hf_mono : Mono f := mono_ofHom_toSpanSingleton k X v hv
  have hf_ne : f ≠ 0 := ofHom_toSpanSingleton_ne_zero k X v hv
  have hf_iso : IsIso f := (Simple.mono_isIso_iff_nonzero f).mpr hf_ne
  exact (asIso f).symm

/-- The additive map sending a `k`-linear map `X →ₗ[k] Y` to its packaging as
a morphism `X ⟶ Y` in `FGModuleCat k`. -/
def ofHomAddHom (X Y : FGModuleCat.{u} k) : (↑X →ₗ[k] ↑Y) →+ (X ⟶ Y) where
  toFun := FGModuleCat.ofHom
  map_zero' := rfl
  map_add' _ _ := rfl

end VecSemisimple
end
