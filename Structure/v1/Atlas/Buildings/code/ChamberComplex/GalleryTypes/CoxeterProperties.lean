/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/CoxeterProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part3
public import Theorem.List.All.of.All.IsChain.Ne
public import Theorem.List.ImageGalleryStutters.is.GalleryStuttersUnderToFun
public import Lemma.Fin.Simple
public import Lemma.Set.EqSimpleDeletionImpliesCoxeterSystem.of.SatisfiesDeletionConditionGen.EqClosure_Range_Top.All_NeMul_1.All_EqMul_1
public import Def.v1.Atlas.Buildings.code.ChamberComplex.UniquenessBook
public import Def.v1.Atlas.Buildings.code.Building.CoxeterComplexFoldings
public import Theorem.Finset.Any_All_IsFacetToSimplicialComplex.of.IsMaximalToSimplicialComplex.IsFacetToSimplicialComplex.All_Any_And_IsMaximalToSimplicialComplexAndIsFacetToSimplicialComplex.All_AdjacentToSimplicialComplex.All_ChamberAdjacent.All_Any_And_Eq.All_All_Eq
public import Theorem.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.TitsForwardHelpers
public section

open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace ChamberComplex

/-- The combinatorial *Coxeter properties* of a chamber complex: thinness plus, for every
adjacent pair $C \sim D$, a folding that fixes $C$ and sends $D$ to $C$. -/
structure CoxeterProperties (K : ChamberComplex V) where
  thin : K.IsThin
  folding_maps_adj_to_self : ∀ C D, K.toSimplicialComplex.Adjacent C D →
    ∃ f : Folding K, C.image f.morph.toFun = C ∧ D.image f.morph.toFun = C

end ChamberComplex
