/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Instance.v1.Atlas.LieGroups.code.MaximalQuotients
public import Lemma.Int.Any_EqUeaAction
public import Lemma.Fin.Any_Eq.of.Ne_0
public import Lemma.Complex.Any_Any_And_All_Eq_AdjointAction.All_Finite.of.IsHarishChandraBimodule.IsIrreducible
public import Def.v1.Atlas.LieGroups.code.HighestWeightModules.Part2
public import Theorem.v1.Atlas.LieGroups.code.HarishChandraCorollaries
public import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part7


public noncomputable section

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

structure IsInHCBimod
    (M : LieBimodule R 𝔤)
    (θ χ : CentralCharacter R 𝔤) : Prop where
  isHC : IsHarishChandraBimodule M
  charPair : M.HasInfinitesimalCharacterPair θ χ

end
