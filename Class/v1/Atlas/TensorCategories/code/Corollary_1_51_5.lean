/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_51_5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
open scoped TensorProduct

universe u₁ u₂


namespace CategoryTheory

/-- A quasi-Hopf algebra structure on a `k`-algebra `H` (Definition 1.35.2): the data of a
comultiplication and counit satisfying counit axioms, an invertible associator `Φ`, an
anti-multiplicative antipode and distinguished elements `α`, `β`, together with the left
`H`-module structure on the linear dual. -/
class IsQuasiHopfAlgebra (k : Type u₁) (H : Type u₂)
    [Field k] [Ring H] [Algebra k H] where
  comul : H →ₐ[k] H ⊗[k] H
  counit : H →ₐ[k] k
  rTensor_counit_comp_comul :
    counit.toLinearMap.rTensor H ∘ₗ comul.toLinearMap = (TensorProduct.mk k k H) 1
  lTensor_counit_comp_comul :
    counit.toLinearMap.lTensor H ∘ₗ comul.toLinearMap = (TensorProduct.mk k H k).flip 1
  Φ : H ⊗[k] H ⊗[k] H
  Φ_invertible : ∃ Ψ : H ⊗[k] H ⊗[k] H, Φ * Ψ = 1 ∧ Ψ * Φ = 1
  antipode : H ≃ₗ[k] H
  antipode_anti_mul : ∀ x y : H, antipode (x * y) = antipode y * antipode x
  antipode_one : antipode 1 = 1
  α : H
  β : H
  leftModuleDual : Module H (Module.Dual k H)

end CategoryTheory
