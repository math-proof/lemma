module
public import Def.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part3
public import Theorem.List.All.of.All.IsChain.Ne
public import Theorem.List.ImageGalleryStutters.is.GalleryStuttersUnderToFun
public import Theorem.Fin.Simple
public import Theorem.Set.EqSimpleDeletionImpliesCoxeterSystem.of.SatisfiesDeletionConditionGen.EqClosure_Range_Top.All_NeMul_1.All_EqMul_1
public import Def.v1.Atlas.Buildings.code.ChamberComplex.UniquenessBook
public import Def.v1.Atlas.Buildings.code.Building.CoxeterComplexFoldings
public import Theorem.Finset.Any_All_RightarrowIsMaximal_RightarrowEq_IsFacet.of.IsMaximal.IsFacet.All_RightarrowIsFacet__RightarrowIsMaximal_Any_And.All_RightarrowIsMaximal_Rightarrow_Rightarrow.All_Rightarrow.All_Any_And.All_RightarrowIsMaximal_All_Rightarrow
public import Theorem.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.TitsForwardHelpers
public import Structure.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterProperties
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

/-- Two chambers $C, D$ are *separated by a wall* if some reversible folding places them on
opposite sides. -/
def SeparatedByWall (K : ChamberComplex V) (C D : Finset V) : Prop :=
  ∃ rf : ReversibleFolding K,
    OppositeSides rf.f C D

/-- $K$ is a *Coxeter complex*: it carries a bijective labelling $\varphi : \text{chambers} \to W$
into a Coxeter group $W$ such that adjacency corresponds to right multiplication by a simple
generator, every facet is shared by at least one other chamber. -/
def IsCoxeterComplex (K : ChamberComplex V) : Prop :=
  ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (φ : Finset V → M.Group),
    (∀ C, K.toSimplicialComplex.IsMaximal C →
      ∀ D, K.toSimplicialComplex.IsMaximal D →
        φ C = φ D → C = D) ∧
    (∀ w : M.Group, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w) ∧
    (∀ C C', K.toSimplicialComplex.Adjacent C C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) ∧
    (∀ C C', K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C') →
        K.toSimplicialComplex.Adjacent C C') ∧
    (∀ F C, K.toSimplicialComplex.IsFacet F C →
      K.toSimplicialComplex.IsMaximal C →
      ∃ D, D ≠ C ∧ K.toSimplicialComplex.IsMaximal D ∧
        K.toSimplicialComplex.IsFacet F D)

/-- $K$ *has sufficient reversible foldings*: every adjacent pair admits a reversible folding
swapping them as boundary chambers of the wall. -/
def HasSufficientReversibleFoldings (K : ChamberComplex V) : Prop :=
  ∀ C D : Finset V,
    K.toSimplicialComplex.Adjacent C D →
    ∃ (rf : ReversibleFolding K),
      C.image rf.f.morph.toFun = C ∧ D.image rf.f.morph.toFun = C ∧
      D.image rf.g.morph.toFun = D ∧ C.image rf.g.morph.toFun = D

end ChamberComplex
