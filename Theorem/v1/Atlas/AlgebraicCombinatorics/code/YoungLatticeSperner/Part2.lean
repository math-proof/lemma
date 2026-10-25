/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part7
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.QuotientIsoLmn
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.GroupActions
import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungLatticeSperner.Part2
set_option autoImplicit false


noncomputable section

open scoped Classical Pointwise

open SpernerProperty YoungLattice YoungLattice.Lmn

open QuotientIsoLmn GroupActions WreathOrbits Finset MulAction

namespace YoungLattice.Lmn

variable {m n : ℕ}

lemma sumParts_gridYoungToLmn (S : GridYoungDiagram m n) :
    sumParts (gridYoungToLmn S) = S.val.card := by
  simp only [sumParts, gridYoungToLmn]
  exact sum_rowSize_eq_card S.val

lemma grade_composed_iso (A : Finset (Fin (m * n))) :
    letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n)
    grade ℕ ((wreathQuotientIsoLmn m n)
      (wreathQuotientMk (A.image finProdFinEquiv.symm))) =
    A.card := by
  letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n)
  rw [grade_eq]
  show sumParts ((wreathQuotientIsoLmn m n) (wreathQuotientMk (A.image finProdFinEquiv.symm))) =
    A.card
  let S := A.image finProdFinEquiv.symm
  have hunfold : (wreathQuotientIsoLmn m n) (wreathQuotientMk S) =
      gridYoungToLmn ⟨canonicalYoung S, canonicalYoung_isGridYoung S⟩ := by
    simp [wreathQuotientIsoLmn, wreathQuotientIsoGridYoung, wreathQuotientToGridYoung,
      quotientIsoLmn, wreathQuotientMk]
  rw [hunfold, sumParts_gridYoungToLmn]
  have hco : SameOrbit (canonicalYoung S) S :=
    (sameOrbit_iff_rowSizeMultiset_eq _ _).mpr
      ((sameOrbit_iff_rowSizeMultiset_eq _ _).mp (canonicalYoung_sameOrbit S)).symm
  rw [card_eq_of_sameOrbit hco]
  exact Finset.card_image_of_injective A finProdFinEquiv.symm.injective

end YoungLattice.Lmn
end
