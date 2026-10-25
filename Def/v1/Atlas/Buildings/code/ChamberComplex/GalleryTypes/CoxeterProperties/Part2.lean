/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/CoxeterProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part3
import Lemma.List.All.of.All.IsChain.Ne
import Lemma.List.ImageGalleryStutters.is.GalleryStuttersUnderToFun
import Lemma.Fin.Simple
import Lemma.Set.EqSimpleDeletionImpliesCoxeterSystem.of.SatisfiesDeletionConditionGen.EqClosure_Range_Top.All_NeMul_1.All_EqMul_1
import Def.v1.Atlas.Buildings.code.ChamberComplex.UniquenessBook
import Def.v1.Atlas.Buildings.code.Building.CoxeterComplexFoldings
import Lemma.Finset.Any_All_IsFacetToSimplicialComplex.of.IsMaximalToSimplicialComplex.IsFacetToSimplicialComplex.All_Any_And_IsMaximalToSimplicialComplexAndIsFacetToSimplicialComplex.All_AdjacentToSimplicialComplex.All_ChamberAdjacent.All_Any_And_Eq.All_All_Eq
import Theorem.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.TitsForwardHelpers
import Theorem.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterProperties
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace ChamberComplex

/-- Assemble `CoxeterProperties K` from thinness plus sufficient reversible foldings. -/
def coxeterProperties_of_hasSufficientReversibleFoldings
    (K : ChamberComplex V) (hThin : K.IsThin)
    (hSRF : HasSufficientReversibleFoldings K) : CoxeterProperties K where
  thin := hThin
  folding_maps_adj_to_self :=
    hasSufficientReversibleFoldings_folding_maps_adj_to_self K hSRF

end ChamberComplex
