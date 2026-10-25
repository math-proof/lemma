/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Lie.OfAssociative
import Structure.v1.Atlas.LieGroups.code.MaximalQuotients.Part2


noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] LieBimodule.instAddCommGroup LieBimodule.instModule

def HomAdEquivariant
    (V : Type*) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (M : LieBimodule R 𝔤) : Submodule R (V →ₗ[R] M.carrier) where
  carrier := { f | ∀ (x : 𝔤) (v : V), f ⁅x, v⁆ = M.adjointAction x (f v) }
  add_mem' := fun {f g} hf hg x v => by
    simp [LinearMap.add_apply, hf x v, hg x v, map_add]
  zero_mem' := fun x v => by simp
  smul_mem' := fun c {f} hf x v => by
    simp [LinearMap.smul_apply, hf x v, map_smul]

end
