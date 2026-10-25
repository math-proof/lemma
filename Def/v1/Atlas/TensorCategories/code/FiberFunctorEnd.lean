/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiberFunctorEnd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Maps
import Theorem.v1.Atlas.TensorCategories.code.FiberFunctorEnd
set_option maxHeartbeats 800000


noncomputable section

open TensorProduct

namespace FiberFunctorEnd

variable (k : Type*) [CommSemiring k]

variable (M N : Type*) [AddCommMonoid M] [AddCommMonoid N]
  [Module k M] [Module k N]

/-- The canonical `k`-algebra homomorphism `End(M) ⊗ End(N) →ₐ End(M ⊗ N)` obtained by
combining right- and left-tensoring with the universal property of the algebra tensor
product. -/
def endTensorEndAlgHom :
    (Module.End k M) ⊗[k] (Module.End k N) →ₐ[k] Module.End k (M ⊗[k] N) :=
  Algebra.TensorProduct.lift
    (Module.End.rTensorAlgHom k M N)
    (Module.End.lTensorAlgHom k N M)
    (rTensor_lTensor_commute k M N)

/-- For finite free `k`-modules `M` and `N`, the canonical algebra map upgrades to a
`k`-algebra isomorphism `End(M) ⊗ End(N) ≃ₐ End(M ⊗ N)`. -/
def endTensorEndAlgEquiv :
    (Module.End k M) ⊗[k] (Module.End k N) ≃ₐ[k] Module.End k (M ⊗[k] N) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
    (homTensorHomEquiv k M N M N)
    (fun φ₁ φ₂ ψ₁ ψ₂ => by
      simp only [homTensorHomEquiv_apply, homTensorHomMap_apply]
      exact TensorProduct.map_mul φ₁ φ₂ ψ₁ ψ₂)
    (by simp [homTensorHomMap_apply])

/-- Named alias of `endTensorEndAlgEquiv`, used as a downstream reference. -/
def endTensorEndAlgEquiv_named :
    (Module.End k M) ⊗[k] (Module.End k N) ≃ₐ[k] Module.End k (M ⊗[k] N) :=
  endTensorEndAlgEquiv k M N

end FiberFunctorEnd
end
