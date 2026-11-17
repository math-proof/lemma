/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/LieSimplicityBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Algebra.Lie.Submodule
public import Mathlib.RingTheory.SimpleModule.Basic

@[expose] public section

noncomputable section

variable {R : Type*} [CommRing R]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

variable [Module (UniversalEnvelopingAlgebra R L) M]

variable [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]

def LieSubmodule.ofUEASubmodule
    (hcompat : ∀ (x : L) (m : M),
      ⁅x, m⁆ = (UniversalEnvelopingAlgebra.ι R (L := L) x) • m)
    (N : Submodule (UniversalEnvelopingAlgebra R L) M) : LieSubmodule R L M where
  carrier := N.carrier
  add_mem' := N.add_mem'
  zero_mem' := N.zero_mem'
  smul_mem' r m hm := by
    have h : (algebraMap R (UniversalEnvelopingAlgebra R L) r) • m ∈ N :=
      N.smul_mem (algebraMap R (UniversalEnvelopingAlgebra R L) r) hm
    rwa [algebraMap_smul] at h
  lie_mem {x m} hm := by
    rw [hcompat x m]
    exact N.smul_mem _ hm

end
