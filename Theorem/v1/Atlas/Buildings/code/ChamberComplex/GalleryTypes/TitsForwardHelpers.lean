/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/TitsForwardHelpers.lean -/

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
import Lemma.Set.InjectiveDeletionCanonicalHom.of.SatisfiesDeletionConditionGen.EqClosure_Range_Top.All_NeMul_1.All_EqMul_1
import Def.v1.Atlas.Buildings.code.ChamberComplex.UniquenessBook
import Def.v1.Atlas.Buildings.code.Building.CoxeterComplexFoldings
import Lemma.Finset.Any_All_IsFacetToSimplicialComplex.of.IsMaximalToSimplicialComplex.IsFacetToSimplicialComplex.All_Any_And_IsMaximalToSimplicialComplexAndIsFacetToSimplicialComplex.All_AdjacentToSimplicialComplex.All_ChamberAdjacent.All_Any_And_Eq.All_All_Eq
import Def.v1.Atlas.Buildings.code.CoxeterGroup.DeletionInjectivity
open scoped Classical


namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- Under the deletion-condition Coxeter system construction, the abstract simple reflection
equals the original generator $\text{gen}(s)$. -/
theorem deletion_coxeter_simple_eq_gen
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (hgen_surj : Subgroup.closure (Set.range gen) = ⊤)
    (hDel : SatisfiesDeletionConditionGen gen) (s : B) :
    (deletion_implies_coxeter_system gen hgen_inv hgen_ne hgen_surj hDel).simple s = gen s := by
  exact deletionCanonicalHom_apply_simple gen hgen_inv hgen_ne s

/-- The `mulEquiv` of a `CoxeterSystem` sends its abstract simple reflection to the simple
reflection of the canonical Coxeter system associated to the matrix $M$. -/
theorem mulEquiv_simple_eq_toCoxeterSystem_simple
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (s : B) :
    cs.mulEquiv (cs.simple s) = M.toCoxeterSystem.simple s := by


  simp [CoxeterSystem.simple, CoxeterMatrix.toCoxeterSystem]

/-- The `mulEquiv` of the deletion-condition Coxeter system maps a generator to the corresponding
simple reflection of the canonical Coxeter system. -/
theorem deletion_coxeter_mulEquiv_gen
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (hgen_surj : Subgroup.closure (Set.range gen) = ⊤)
    (hDel : SatisfiesDeletionConditionGen gen) (s : B) :
    (deletion_implies_coxeter_system gen hgen_inv hgen_ne hgen_surj hDel).mulEquiv (gen s) =
      (deletionCoxeterMatrix gen hgen_inv hgen_ne).toCoxeterSystem.simple s := by
  rw [← deletion_coxeter_simple_eq_gen gen hgen_inv hgen_ne hgen_surj hDel s]
  exact mulEquiv_simple_eq_toCoxeterSystem_simple _ s

end CoxeterSystemFromDeletion
