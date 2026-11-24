module
public import Def.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part3
public import Theorem.List.All.of.All.IsChain.Ne
public import Theorem.List.ImageGalleryStutters.is.GalleryStuttersUnderToFun
public import Theorem.Fin.Simple
public import Theorem.Set.EqSimpleDeletionImpliesCoxeterSystem.of.SatisfiesDeletionConditionGen.EqClosure_Range_Top.All_NeMul_1.All_EqMul_1
public import Def.v1.Atlas.Buildings.code.ChamberComplex.UniquenessBook
public import Def.v1.Atlas.Buildings.code.Building.CoxeterComplexFoldings
public import Theorem.Finset.Any_All_IsFacetToSimplicialComplex.of.IsMaximalToSimplicialComplex.IsFacetToSimplicialComplex.All_Any_And_IsMaximalToSimplicialComplexAndIsFacetToSimplicialComplex.All_AdjacentToSimplicialComplex.All_ChamberAdjacent.All_Any_And_Eq.All_All_Eq
public import Theorem.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.TitsForwardHelpers
public import Def.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterProperties
open scoped Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/CoxeterProperties.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {V : Type*} [DecidableEq V]


namespace ChamberComplex

/-- Sufficient reversible foldings give the "folding maps adjacent to self" condition. -/
theorem hasSufficientReversibleFoldings_folding_maps_adj_to_self
    (K : ChamberComplex V) (hSRF : HasSufficientReversibleFoldings K) :
    ∀ C D, K.toSimplicialComplex.Adjacent C D →
      ∃ f : Folding K, C.image f.morph.toFun = C ∧ D.image f.morph.toFun = C := by
  intro C D hadj
  obtain ⟨rf, hfC, hfD_eq_C, _, _⟩ := hSRF C D hadj
  exact ⟨rf.f, hfC, hfD_eq_C⟩

end ChamberComplex
