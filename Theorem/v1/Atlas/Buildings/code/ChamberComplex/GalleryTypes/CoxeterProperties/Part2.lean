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
import Def.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterProperties.Part2
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace ChamberComplex

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

end ChamberComplex
