/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/CoxeterProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.Folding
import Lemma.List.All.of.All.IsChain.Ne
import Lemma.List.ImageGalleryStutters.is.GalleryStuttersUnderToFun
import Lemma.Fin.Simple
import Lemma.Set.EqSimpleDeletionImpliesCoxeterSystem.of.SatisfiesDeletionConditionGen.EqClosure_Range_Top.All_NeMul_1.All_EqMul_1
import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.UniquenessBook
import sympy.atlas.v1.Atlas.Buildings.code.Building.CoxeterComplexFoldings
import Lemma.Finset.Any_All_IsFacetToSimplicialComplex.of.IsMaximalToSimplicialComplex.IsFacetToSimplicialComplex.All_Any_And_IsMaximalToSimplicialComplexAndIsFacetToSimplicialComplex.All_AdjacentToSimplicialComplex.All_ChamberAdjacent.All_Any_And_Eq.All_All_Eq
import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.TitsForwardHelpers

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace ChamberComplex

/-- The combinatorial *Coxeter properties* of a chamber complex: thinness plus, for every
adjacent pair $C \sim D$, a folding that fixes $C$ and sends $D$ to $C$. -/
structure CoxeterProperties (K : ChamberComplex V) where
  thin : K.IsThin
  folding_maps_adj_to_self : ∀ C D, K.toSimplicialComplex.Adjacent C D →
    ∃ f : Folding K, C.image f.morph.toFun = C ∧ D.image f.morph.toFun = C

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

/-- Sufficient reversible foldings give the "folding maps adjacent to self" condition. -/
theorem hasSufficientReversibleFoldings_folding_maps_adj_to_self
    (K : ChamberComplex V) (hSRF : HasSufficientReversibleFoldings K) :
    ∀ C D, K.toSimplicialComplex.Adjacent C D →
      ∃ f : Folding K, C.image f.morph.toFun = C ∧ D.image f.morph.toFun = C := by
  intro C D hadj
  obtain ⟨rf, hfC, hfD_eq_C, _, _⟩ := hSRF C D hadj
  exact ⟨rf.f, hfC, hfD_eq_C⟩

/-- Assemble `CoxeterProperties K` from thinness plus sufficient reversible foldings. -/
def coxeterProperties_of_hasSufficientReversibleFoldings
    (K : ChamberComplex V) (hThin : K.IsThin)
    (hSRF : HasSufficientReversibleFoldings K) : CoxeterProperties K where
  thin := hThin
  folding_maps_adj_to_self :=
    hasSufficientReversibleFoldings_folding_maps_adj_to_self K hSRF

/-- Converse of the characterization: a thin chamber complex with sufficient foldings is a
Coxeter complex. -/
theorem thinWithFoldings_isCoxeterComplex
    {V : Type*} [DecidableEq V] (K : ChamberComplex V) :
    K.IsThin → AptIsCoxeterProof.HasSufficientFoldings K → IsCoxeterComplex K := by
  intro hThin hSF

  obtain ⟨B, W, instW, gen, φ_W, hgen_inv, hgen_ne, hgen_surj, hDel,
          hinj, hsurj, hadj_fwd, hadj_bwd, hfacet⟩ :=
    ChamberComplex.tits_forward_construction K hThin hSF

  letI := instW
  let cs := CoxeterSystemFromDeletion.deletion_implies_coxeter_system
    gen hgen_inv hgen_ne hgen_surj hDel
  let M := CoxeterSystemFromDeletion.deletionCoxeterMatrix gen hgen_inv hgen_ne

  let φ' : Finset V → M.Group := fun C => cs.mulEquiv (φ_W C)

  refine ⟨B, M, φ', ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro C hCmax D hDmax hφ'eq
    have hφeq : φ_W C = φ_W D := cs.mulEquiv.injective hφ'eq
    exact hinj C hCmax D hDmax hφeq
  ·
    intro w
    obtain ⟨C, hCmax, hφC⟩ := hsurj (cs.mulEquiv.symm w)
    exact ⟨C, hCmax, by simp [φ', hφC]⟩
  ·
    intro C C' hadj_CC'
    obtain ⟨s, hs⟩ := hadj_fwd C C' hadj_CC'
    constructor
    ·
      intro heq
      have : φ_W C = φ_W C' := cs.mulEquiv.injective heq
      exact hadj_CC'.2.2.1 (hinj C hadj_CC'.1 C' hadj_CC'.2.1 this)
    ·
      use s
      show cs.mulEquiv (φ_W C') = cs.mulEquiv (φ_W C) * M.toCoxeterSystem.simple s
      rw [hs, map_mul, CoxeterSystemFromDeletion.deletion_coxeter_mulEquiv_gen
        gen hgen_inv hgen_ne hgen_surj hDel s]
  ·
    intro C C' hCmax hC'max hadj_grp
    obtain ⟨_, i, hi⟩ := hadj_grp


    have hgen_eq := CoxeterSystemFromDeletion.deletion_coxeter_mulEquiv_gen
      gen hgen_inv hgen_ne hgen_surj hDel i
    have hW : φ_W C' = φ_W C * gen i := by
      apply cs.mulEquiv.injective
      rw [map_mul, hgen_eq]
      exact hi
    exact hadj_bwd C C' i hCmax hC'max hW
  ·
    exact hfacet
