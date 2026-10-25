/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Goal77_Cor134_Status.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.KostantTheorem.Part5
import Lemma.Int.Zero.in.DominantWeights


example {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) :
    (Fintype.card ksd.W : ℤ) • (concreteCT_posRoots ksd.roots ksd.posRoots : PowerSeries ℤ) =
      concreteCT_fullRoots ksd.roots ∧
    (∏ i : Fin ksd.rank, qInteger (ksd.degrees i)) *
      (concreteCT_posRoots ksd.roots ksd.posRoots : PowerSeries ℤ) = 1 :=
  corollary_13_4 ksd

