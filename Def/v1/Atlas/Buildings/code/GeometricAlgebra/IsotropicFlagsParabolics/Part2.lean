/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/IsotropicFlagsParabolics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Lemma.Submodule.OfEq.eq.M.of.Eq
import Lemma.Fin.Eq.of.Ne_0.All_Eq
import Lemma.Submodule.Any_EqMapToLinearMap.of.FinrankK
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.WittTheorem.Part2
import Instance.v1.Atlas.Buildings.code.GeometricAlgebra.FlagEquivalenceInstance
import Structure.v1.Atlas.Buildings.code.GeometricAlgebra.IsotropicFlagsParabolics


namespace Garrett

variable {k : Type*} [Field k] [DecidableEq k] [NeZero (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V]


variable {B : LinearMap.BilinForm k V}

/-- The type of an isotropic flag is the sequence of dimensions of its spaces. -/
noncomputable def IsotropicFlag.flagType (F : IsotropicFlag B) : Fin F.len → ℕ :=
  fun i => Module.finrank k (F.spaces i)

/-- Two isotropic flags have the same type if they have the same length and the
same dimension sequence. -/
def IsotropicFlag.sameType (F₁ F₂ : IsotropicFlag B) : Prop :=
  F₁.len = F₂.len ∧
  ∀ (h : F₁.len = F₂.len) (i : Fin F₁.len),
    Module.finrank k (F₁.spaces i) = Module.finrank k (F₂.spaces (Fin.cast h i))


/-- The parabolic subgroup of an isotropic flag `F` consists of all global
isometries of `B` that stabilize every space of `F` setwise. -/
def IsotropicFlag.parabolicSubgroup (F : IsotropicFlag B) : Set (V ≃ₗ[k] V) :=
  { Φ | IsGlobalIsometry B Φ ∧ ∀ i, (F.spaces i).map Φ.toLinearMap = F.spaces i }

/-- Restriction of a linear automorphism `e : M ≃ₗ M` to a linear equivalence
`U ≃ₗ W` between subspaces `U` and `W = e(U)`. -/
noncomputable def LinearEquiv.restrictSubmodule {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (e : M ≃ₗ[R] M) (U W : Submodule R M)
    (h : U.map e.toLinearMap = W) : U ≃ₗ[R] W :=
  (e.submoduleMap U).trans (LinearEquiv.ofEq _ _ h)

end Garrett
