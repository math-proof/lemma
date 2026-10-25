/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/Prod.lean -/

import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Def.LinearAlgebra.BilinearForm.Prod
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

/-- Evaluation formula for the orthogonal product of bilinear forms. -/
@[simp]
theorem prod_apply (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂)
    (x y : M₁ × M₂) :
    B₁.prod B₂ x y = B₁ x.1 y.1 + B₂ x.2 y.2 :=
  rfl

end Prod
end BilinForm
end LinearMap
