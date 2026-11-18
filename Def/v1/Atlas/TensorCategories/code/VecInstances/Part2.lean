/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
public import Theorem.v1.Atlas.TensorCategories.code.VecInstances.Part3

@[expose] public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u


noncomputable section

namespace VecInstances

section FiniteLength

variable (k : Type u) [Field k]

/-- The `k`-algebra homomorphism `End(𝟙_ Vec) →ₐ[k] k` sending an endomorphism `f`
to `f(1)`, witnessing the identification of `End(𝟙_ Vec)` with `k`. -/
noncomputable def endUnitAlgHom : End (𝟙_ (FGModuleCat k)) →ₐ[k] k where
  toFun f := f.asHom.hom 1
  map_one' := by simp
  map_mul' := by
    intro f g

    change f.asHom.hom (g.asHom.hom 1) = f.asHom.hom 1 * g.asHom.hom 1

    set a := g.asHom.hom 1
    calc f.asHom.hom a = f.asHom.hom (a • (1 : k)) := by rw [smul_eq_mul, mul_one]
      _ = a • f.asHom.hom 1 := by rw [map_smul]
      _ = a * f.asHom.hom 1 := by rw [smul_eq_mul]
      _ = f.asHom.hom 1 * a := by ring
  map_zero' := by change (0 : k →ₗ[k] k) 1 = 0; simp
  map_add' := by
    intro f g; change (f.asHom.hom + g.asHom.hom) 1 = f.asHom.hom 1 + g.asHom.hom 1; simp
  commutes' := by
    intro c
    change ((c • (1 : End (𝟙_ (FGModuleCat k)))).asHom.hom.hom) 1 = c
    rw [End.smul_asHom, End.one_asHom]
    change (c • (LinearMap.id : k →ₗ[k] k)) 1 = c
    simp [LinearMap.smul_apply]

/-- The `k`-algebra isomorphism `End(𝟙_ Vec) ≃ₐ[k] k`, upgrading `endUnitAlgHom`
into a bijection. This realizes `End(𝟙) ≅ k` for `Vec_k`. -/
noncomputable def endUnitAlgEquiv : End (𝟙_ (FGModuleCat k)) ≃ₐ[k] k :=
  AlgEquiv.ofBijective (endUnitAlgHom k) ⟨by
    intro f g hfg
    simp only [endUnitAlgHom, AlgHom.coe_mk, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk] at hfg
    exact End.ext
      (InducedCategory.Hom.ext
        (ModuleCat.Hom.ext (linearMap_eq_of_apply_one k _ _ hfg)))
  , by
    intro c
    exact ⟨algebraMap k _ c, by
      simp only [endUnitAlgHom, AlgHom.coe_mk, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk]
      change ((c • (1 : End (𝟙_ (FGModuleCat k)))).asHom.hom.hom) 1 = c
      rw [End.smul_asHom, End.one_asHom]
      change (c • (LinearMap.id : k →ₗ[k] k)) 1 = c
      simp [LinearMap.smul_apply]⟩
  ⟩

end FiniteLength
end VecInstances
end
