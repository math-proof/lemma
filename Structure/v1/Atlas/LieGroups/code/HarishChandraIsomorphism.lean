/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Theorem.v1.Atlas.LieGroups.code.PBW
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Def.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open TriangularDecomposition

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

structure WeylGroupData (Δ : TriangularDecomposition R 𝔤) where
  W : Type*
  [instGroup : Group W]
  [instFintype : Fintype W]
  algAction : W →* (UniversalEnvelopingAlgebra R Δ.𝔥) ≃ₐ[R]
    (UniversalEnvelopingAlgebra R Δ.𝔥)
  ρ : Δ.𝔥 →ₗ[R] R

  dualAction : W → (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R)
  dualAction_one : ∀ (μ : Δ.𝔥 →ₗ[R] R), dualAction 1 μ = μ
  dualAction_mul : ∀ (w₁ w₂ : W) (μ : Δ.𝔥 →ₗ[R] R),
    dualAction (w₁ * w₂) μ = dualAction w₁ (dualAction w₂ μ)
  dualAction_add : ∀ (w : W) (μ ν : Δ.𝔥 →ₗ[R] R),
    dualAction w (μ + ν) = dualAction w μ + dualAction w ν
  dualAction_smul : ∀ (w : W) (c : R) (μ : Δ.𝔥 →ₗ[R] R),
    dualAction w (c • μ) = c • dualAction w μ
  algDualCompat : ∀ (g : W) (wt : Δ.𝔥 →ₗ[R] R) (p : UniversalEnvelopingAlgebra R Δ.𝔥),
    evalWeight Δ wt ((algAction g) p) = evalWeight Δ (dualAction g⁻¹ wt) p
  orbitSeparation : ∀ (mu nu : Δ.𝔥 →ₗ[R] R),
    (∀ (p : UniversalEnvelopingAlgebra R Δ.𝔥),
      (∀ g : W, (algAction g) p = p) →
      evalWeight Δ mu p = evalWeight Δ nu p) →
    ∃ w : W, nu = dualAction w mu

end
