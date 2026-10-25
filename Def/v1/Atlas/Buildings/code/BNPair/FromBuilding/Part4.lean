/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/FromBuilding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Lemma.Finset.IsMaximalToSimplicialComplex.of.IsMaximal.In_Apartments
import Def.v1.Atlas.Buildings.code.Building.Labels
import Def.v1.Atlas.Buildings.code.Building.RetractionDef
import Structure.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
import Theorem.v1.Atlas.Buildings.code.BNPair.FromBuilding.Part2
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]


namespace BNPairFromBuildingData

variable {V : Type*} [DecidableEq V]
  {G : Type*} [Group G]
  {b : Building V}
  {ct : Building.CoxeterTypeOfBuilding b}
  (data : BNPairFromBuildingData G b ct)

/-- **The strict BN-pair built from the building data.** Bundles $B$, $N$, $T = B \cap N$,
the surjective homomorphism $\pi : N \to W$ with kernel $T$, and the generation property
$\langle B, N \rangle = G$, producing a `BNPair G ct.matrix`. -/
def toBNPair : BNPair G ct.matrix where
  B := data.B
  N := data.N
  T := data.T
  T_eq := data.T_eq_inf
  π := data.π
  π_surj := data.π_surj
  π_ker := data.π_ker
  generates := data.generates

end BNPairFromBuildingData
