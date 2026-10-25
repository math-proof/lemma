/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.LieGroups.code.MaximalQuotients
import Lemma.Int.Any_EqUeaAction
import Lemma.Fin.Any_Eq.of.Ne_0
import Lemma.Complex.Any_Any_And_All_Eq_AdjointAction.All_Finite.of.IsHarishChandraBimodule.IsIrreducible
import Def.v1.Atlas.LieGroups.code.HighestWeightModules.Part2
import Theorem.v1.Atlas.LieGroups.code.HarishChandraCorollaries
import Theorem.v1.Atlas.LieGroups.code.DufloJoseph.Part3


noncomputable section

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

def HomEquivariant
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (N : Type*) [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    Submodule R (M →ₗ[R] N) where
  carrier := { f | ∀ (x : 𝔤) (m : M), f ⁅x, m⁆ = ⁅x, f m⁆ }
  add_mem' := fun {f g} hf hg x m => by
    simp only [LinearMap.add_apply]; rw [hf x m, hg x m, lie_add]
  zero_mem' := fun x m => by simp
  smul_mem' := fun c {f} hf x m => by
    simp only [LinearMap.smul_apply]; rw [hf x m, lie_smul]

def ueaActionFromLieModule
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M :=
  UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)

end
