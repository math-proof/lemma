/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Lie.OfAssociative
public import Structure.v1.Atlas.LieGroups.code.MaximalQuotients.Part2

@[expose] public section

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
