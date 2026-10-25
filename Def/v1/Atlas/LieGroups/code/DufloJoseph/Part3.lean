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
import Theorem.v1.Atlas.LieGroups.code.DufloJoseph.Part2


noncomputable section

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

def HomFinBimodule [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    LieBimodule R 𝔤 where
  carrier := ↥(HomFin (R := R) (𝔤 := 𝔤) M N)
  leftAction := {
    toFun := fun u => {
      toFun := fun ⟨T, hT⟩ => ⟨(UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T,
        leftAction_preserves_HomFin M N u T hT⟩
      map_add' := fun ⟨T₁, _⟩ ⟨T₂, _⟩ => by
        ext m; simp [LinearMap.comp_apply, map_add]
      map_smul' := fun r ⟨T₁, _⟩ => by
        ext m; simp [LinearMap.comp_apply, map_smul]
    }
    map_one' := by ext ⟨T, _⟩ m; simp
    map_mul' := fun u₁ u₂ => by
      ext ⟨T, _⟩ m; simp [Module.End.mul_apply, LinearMap.comp_apply]
    map_zero' := by ext ⟨T, _⟩ m; simp
    map_add' := fun u₁ u₂ => by
      ext ⟨T, _⟩ m; simp [LinearMap.add_apply, LinearMap.comp_apply]
    commutes' := fun r => by
      ext ⟨T, _⟩ m; simp [Module.algebraMap_end_apply]
  }
  rightAction := {
    toFun := fun vop => {
      toFun := fun ⟨T, hT⟩ => ⟨T.comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M) (MulOpposite.unop vop)),
        rightAction_preserves_HomFin M N (MulOpposite.unop vop) T hT⟩
      map_add' := fun ⟨T₁, _⟩ ⟨T₂, _⟩ => by
        ext m; simp [LinearMap.comp_apply]
      map_smul' := fun r ⟨T₁, _⟩ => by
        ext m; simp [LinearMap.comp_apply]
    }
    map_one' := by ext ⟨T, _⟩ m; simp
    map_mul' := fun a b => by
      ext ⟨T, _⟩ m
      simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
        MulOpposite.unop_mul, map_mul]
    map_zero' := by ext ⟨T, _⟩ m; simp
    map_add' := fun a b => by
      ext ⟨T, _⟩ m; simp [MulOpposite.unop_add, LinearMap.add_apply, LinearMap.comp_apply]
    commutes' := fun r => by
      ext ⟨T, _⟩ m
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
        Module.algebraMap_end_apply]
      simp [map_smul]
  }
  actions_commute := fun u v ⟨T, hT⟩ => by
    ext m
    simp [LinearMap.comp_apply]

end
