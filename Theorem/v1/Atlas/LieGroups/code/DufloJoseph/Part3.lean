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
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part3


noncomputable section

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

theorem homFinBimodule_adjointAction_val [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (x : 𝔤) (T : ↥(HomFin (R := R) (𝔤 := 𝔤) M N)) :
    ((HomFinBimodule (R := R) (𝔤 := 𝔤) M N).adjointAction x T).val =
    adjointActionOnHom (R := R) (𝔤 := 𝔤) M N x T.val := by
  unfold HomFinBimodule LieBimodule.adjointAction adjointActionOnHom
  ext m
  simp [LinearMap.sub_apply, LinearMap.comp_apply]

end
