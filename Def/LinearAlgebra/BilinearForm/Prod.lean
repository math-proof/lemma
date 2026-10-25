/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/Prod.lean -/

import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.PerfectPairing.Basic
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

section Prod

variable {R M₁ M₂ : Type*} [CommSemiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

/-- The orthogonal product of two bilinear forms, acting componentwise on
a product of modules. -/
def prod (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) :
    BilinForm R (M₁ × M₂) :=
  B₁.compl₁₂ (LinearMap.fst R M₁ M₂) (LinearMap.fst R M₁ M₂) +
    B₂.compl₁₂ (LinearMap.snd R M₁ M₂) (LinearMap.snd R M₁ M₂)

end Prod
end BilinForm
end LinearMap
