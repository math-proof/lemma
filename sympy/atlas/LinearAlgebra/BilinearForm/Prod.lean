/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/Prod.lean -/

import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Orthogonal product of bilinear forms

This file defines the orthogonal product of two bilinear forms on a product
of modules and proves its basic properties.

## Main definitions

* `BilinForm.prod`: the orthogonal product of two bilinear forms,
  evaluated componentwise.

## Main results

* `BilinForm.prod_apply`: the evaluation formula for the product.
* `BilinForm.nondegenerate_prod_iff`: the product is nondegenerate if and
  only if both factors are.
* `BilinForm.instIsPerfPairProd`: the product of two perfect pairings is a
  perfect pairing.
* `BilinForm.dualSubmodule_prod`: dual submodules commute with products.
-/

open LinearMap (BilinForm)
open Module

namespace LinearMap
namespace BilinForm

section Prod

variable {R M₁ M₂ : Type*} [CommSemiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

/-- The orthogonal product of two bilinear forms, acting componentwise on
a product of modules. -/
def prod (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) :
    BilinForm R (M₁ × M₂) :=
  B₁.compl₁₂ (LinearMap.fst R M₁ M₂) (LinearMap.fst R M₁ M₂) +
    B₂.compl₁₂ (LinearMap.snd R M₁ M₂) (LinearMap.snd R M₁ M₂)

/-- Evaluation formula for the orthogonal product of bilinear forms. -/
@[simp]
theorem prod_apply (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂)
    (x y : M₁ × M₂) :
    B₁.prod B₂ x y = B₁ x.1 y.1 + B₂ x.2 y.2 :=
  rfl

/-- The orthogonal product of two bilinear forms is nondegenerate if and
only if both factors are nondegenerate. -/
@[simp]
theorem nondegenerate_prod_iff {B₁ : BilinForm R M₁}
    {B₂ : BilinForm R M₂} :
    (B₁.prod B₂).Nondegenerate ↔ B₁.Nondegenerate ∧ B₂.Nondegenerate := by
  have sepL : (B₁.prod B₂).SeparatingLeft ↔
      B₁.SeparatingLeft ∧ B₂.SeparatingLeft := by
    constructor
    · intro h
      refine ⟨fun x₁ hx₁ => ?_, fun x₂ hx₂ => ?_⟩
      · have hmem : (x₁, 0) = (0 : M₁ × M₂) :=
          h _ fun y => by simpa using hx₁ y.1
        exact congrArg Prod.fst hmem
      · have hmem : ((0 : M₁), x₂) = (0 : M₁ × M₂) :=
          h _ fun y => by simpa using hx₂ y.2
        exact congrArg Prod.snd hmem
    · rintro ⟨h₁, h₂⟩ x hx
      have e₁ : x.1 = 0 := h₁ _ fun y₁ => by simpa using hx (y₁, 0)
      have e₂ : x.2 = 0 := h₂ _ fun y₂ => by simpa using hx (0, y₂)
      exact Prod.ext e₁ e₂
  have sepR : (B₁.prod B₂).SeparatingRight ↔
      B₁.SeparatingRight ∧ B₂.SeparatingRight := by
    constructor
    · intro h
      refine ⟨fun y₁ hy₁ => ?_, fun y₂ hy₂ => ?_⟩
      · have hmem : (y₁, 0) = (0 : M₁ × M₂) :=
          h _ fun x => by simpa using hy₁ x.1
        exact congrArg Prod.fst hmem
      · have hmem : ((0 : M₁), y₂) = (0 : M₁ × M₂) :=
          h _ fun x => by simpa using hy₂ x.2
        exact congrArg Prod.snd hmem
    · rintro ⟨h₁, h₂⟩ y hy
      have e₁ : y.1 = 0 := h₁ _ fun x₁ => by simpa using hy (x₁, 0)
      have e₂ : y.2 = 0 := h₂ _ fun x₂ => by simpa using hy (0, x₂)
      exact Prod.ext e₁ e₂
  constructor
  · rintro ⟨hL, hR⟩
    exact ⟨⟨(sepL.mp hL).1, (sepR.mp hR).1⟩,
      ⟨(sepL.mp hL).2, (sepR.mp hR).2⟩⟩
  · rintro ⟨⟨h1L, h1R⟩, ⟨h2L, h2R⟩⟩
    exact ⟨sepL.mpr ⟨h1L, h2L⟩, sepR.mpr ⟨h1R, h2R⟩⟩

end Prod

section PerfPair

variable {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]
  [Module R M₁] [Module R M₂]

/-- The orthogonal product of two perfect pairings is a perfect pairing,
via the product of the associated equivalences and duality for products. -/
instance instIsPerfPairProd (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂)
    [B₁.IsPerfPair] [B₂.IsPerfPair] :
    (B₁.prod B₂).IsPerfPair := by
  have hR : Module.IsReflexive R (M₁ × M₂) :=
    @Prod.instModuleIsReflexive _ _ _ _ _ _ _ _
      (Module.IsReflexive.of_isPerfPair (p := B₁))
      (Module.IsReflexive.of_isPerfPair (p := B₂))
  have hmod : B₁.prod B₂ =
      ((B₁.toPerfPair.prodCongr B₂.toPerfPair).trans
        (Module.dualProdDualEquivDual R M₁ M₂)).toLinearMap := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [prod_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.prodCongr_apply, Module.dualProdDualEquivDual_apply,
      LinearMap.coprod_apply, LinearMap.toPerfPair_apply]
  rw [hmod]
  exact @LinearMap.IsPerfPair.of_bijective _ _ _ _ _ _ _ _ _ hR
    (LinearEquiv.bijective _)

end PerfPair

section DualSubmodule

variable {R S M₁ M₂ : Type*} [CommRing R] [Field S]
  [AddCommGroup M₁] [AddCommGroup M₂] [Algebra R S]
  [Module R M₁] [Module R M₂] [Module S M₁] [Module S M₂]
  [IsScalarTower R S M₁] [IsScalarTower R S M₂]

/-- Dual submodules commute with orthogonal products of bilinear forms. -/
@[simp]
theorem dualSubmodule_prod (B₁ : BilinForm S M₁) (B₂ : BilinForm S M₂)
    (N₁ : Submodule R M₁) (N₂ : Submodule R M₂) :
    (B₁.prod B₂).dualSubmodule (N₁.prod N₂) =
      (B₁.dualSubmodule N₁).prod (B₂.dualSubmodule N₂) := by
  ext x
  simp only [mem_dualSubmodule, Submodule.mem_prod]
  constructor
  · rintro h
    refine ⟨fun y₁ hy₁ => ?_, fun y₂ hy₂ => ?_⟩
    · have h0 := h (y₁, 0) ⟨hy₁, Submodule.zero_mem _⟩
      simpa using h0
    · have h0 := h (0, y₂) ⟨Submodule.zero_mem _, hy₂⟩
      simpa using h0
  · rintro ⟨h₁, h₂⟩ y hy
    obtain ⟨hy₁, hy₂⟩ := hy
    simpa [prod_apply] using add_mem (h₁ _ hy₁) (h₂ _ hy₂)

end DualSubmodule

end BilinForm
end LinearMap
