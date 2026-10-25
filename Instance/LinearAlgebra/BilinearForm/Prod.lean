/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/Prod.lean -/

import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Theorem.LinearAlgebra.BilinearForm.Prod
open LinearMap (BilinForm)
open Module

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


namespace LinearMap

namespace BilinForm

section PerfPair

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
end BilinForm
end LinearMap
