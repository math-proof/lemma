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
-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open TriangularDecomposition

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

def Subalgebra.invariants {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]
    (G : Type*) [Group G] (act : G →* A ≃ₐ[R] A) : Subalgebra R A where
  carrier := { a : A | ∀ g : G, (act g) a = a }
  mul_mem' := fun {a b} ha hb g => by simp [map_mul, ha g, hb g]
  one_mem' := fun g => by simp
  add_mem' := fun {a b} ha hb g => by simp [map_add, ha g, hb g]
  zero_mem' := fun g => by simp
  algebraMap_mem' := fun r g => by simp [AlgEquiv.commutes]

end
