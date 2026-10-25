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
import Def.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part3
-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open TriangularDecomposition

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] WeylGroupData.instGroup WeylGroupData.instFintype

theorem pbw_triangular_iso_one (Δ : TriangularDecomposition R 𝔤) :
    pbw_triangular_iso R 𝔤 Δ 1 = 1 := by
  sorry

theorem LinearMap.exists_factor_of_surjective_ker_le
    {R' : Type*} [CommRing R']
    {A B C : Type*} [AddCommGroup A] [Module R' A]
    [AddCommGroup B] [Module R' B] [AddCommGroup C] [Module R' C]
    {p : A →ₗ[R'] B} {f : A →ₗ[R'] C}
    (hsurj : Function.Surjective p) (hker : LinearMap.ker p ≤ LinearMap.ker f) :
    ∃ (ℓ : B →ₗ[R'] C), ∀ a, ℓ (p a) = f a := by
  sorry

end
