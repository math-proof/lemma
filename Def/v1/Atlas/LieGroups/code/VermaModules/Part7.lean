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
import Theorem.v1.Atlas.LieGroups.code.VermaModules.Part2


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

namespace TriangularDecomposition

variable (Δ : TriangularDecomposition R 𝔤)

def lieModuleEquivOfSurjEqKer
    {M₀ V₁ V₂ : Type*}
    [AddCommGroup M₀] [Module R M₀] [LieRingModule 𝔤 M₀] [LieModule R 𝔤 M₀]
    [AddCommGroup V₁] [Module R V₁] [LieRingModule 𝔤 V₁] [LieModule R 𝔤 V₁]
    [AddCommGroup V₂] [Module R V₂] [LieRingModule 𝔤 V₂] [LieModule R 𝔤 V₂]
    (η₁ : M₀ →ₗ⁅R,𝔤⁆ V₁) (hη₁ : Function.Surjective η₁)
    (η₂ : M₀ →ₗ⁅R,𝔤⁆ V₂) (hη₂ : Function.Surjective η₂)
    (hker : η₁.ker = η₂.ker) : V₁ ≃ₗ⁅R,𝔤⁆ V₂ := by
  have hker_sub : η₁.toLinearMap.ker = η₂.toLinearMap.ker :=
    congr_arg LieSubmodule.toSubmodule hker
  have h12 : η₁.toLinearMap.ker ≤ η₂.toLinearMap.ker := le_of_eq hker_sub
  have h21 : η₂.toLinearMap.ker ≤ η₁.toLinearMap.ker := le_of_eq hker_sub.symm

  let f_lin : V₁ →ₗ[R] V₂ :=
    (η₁.toLinearMap.ker.liftQ η₂.toLinearMap h12).comp
      (η₁.toLinearMap.quotKerEquivOfSurjective hη₁).symm.toLinearMap

  let g_lin : V₂ →ₗ[R] V₁ :=
    (η₂.toLinearMap.ker.liftQ η₁.toLinearMap h21).comp
      (η₂.toLinearMap.quotKerEquivOfSurjective hη₂).symm.toLinearMap

  have hf : ∀ m, f_lin (η₁ m) = η₂ m := fun m =>
    liftQ_comp_quotKerEquiv_symm_apply η₁.toLinearMap hη₁ η₂.toLinearMap h12 m
  have hg : ∀ m, g_lin (η₂ m) = η₁ m := fun m =>
    liftQ_comp_quotKerEquiv_symm_apply η₂.toLinearMap hη₂ η₁.toLinearMap h21 m
  exact LieModuleEquiv.mk
    { toLinearMap := f_lin
      map_lie' := by
        intro x v₁; obtain ⟨m, rfl⟩ := hη₁ v₁
        change f_lin (⁅x, η₁ m⁆) = ⁅x, f_lin (η₁ m)⁆
        rw [← η₁.map_lie, hf, hf, η₂.map_lie] }
    g_lin
    (fun v₁ => by
      obtain ⟨m, rfl⟩ := hη₁ v₁; change g_lin (f_lin (η₁ m)) = η₁ m; rw [hf, hg])
    (fun v₂ => by
      obtain ⟨m, rfl⟩ := hη₂ v₂; change f_lin (g_lin (η₂ m)) = η₂ m; rw [hg, hf])

end TriangularDecomposition
end
