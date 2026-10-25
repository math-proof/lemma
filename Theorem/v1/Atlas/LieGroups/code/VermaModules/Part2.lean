/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Order.Atoms
import Mathlib.RingTheory.Congruence.Defs
import Def.v1.Atlas.LieGroups.code.VermaModules.Part6


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

namespace TriangularDecomposition

variable (Δ : TriangularDecomposition R 𝔤)

theorem liftQ_comp_quotKerEquiv_symm_apply
    {M₀ : Type*} [AddCommGroup M₀] [Module R M₀]
    {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    (f₁ : M₀ →ₗ[R] N₁) (hf₁ : Function.Surjective f₁)
    (f₂ : M₀ →ₗ[R] N₂) (h : f₁.ker ≤ f₂.ker) (m : M₀) :
    (f₁.ker.liftQ f₂ h) ((f₁.quotKerEquivOfSurjective hf₁).symm (f₁ m)) = f₂ m := by
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]; rfl

end TriangularDecomposition
end
