/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiberFunctorEnd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Maps
set_option maxHeartbeats 800000


noncomputable section

open TensorProduct

namespace FiberFunctorEnd

variable (k : Type*) [CommSemiring k]

variable (M N : Type*) [AddCommMonoid M] [AddCommMonoid N]
  [Module k M] [Module k N]

/-- Right-tensoring by `φ : End M` and left-tensoring by `ψ : End N` commute as
endomorphisms of `M ⊗ N`. -/
theorem rTensor_lTensor_commute (φ : Module.End k M) (ψ : Module.End k N) :
    Commute (Module.End.rTensorAlgHom k M N φ) (Module.End.lTensorAlgHom k N M ψ) := by
  show LinearMap.rTensor N φ * LinearMap.lTensor M ψ =
    LinearMap.lTensor M ψ * LinearMap.rTensor N φ
  show (LinearMap.rTensor N φ).comp (LinearMap.lTensor M ψ) =
    (LinearMap.lTensor M ψ).comp (LinearMap.rTensor N φ)
  ext m n; simp

end FiberFunctorEnd
end
