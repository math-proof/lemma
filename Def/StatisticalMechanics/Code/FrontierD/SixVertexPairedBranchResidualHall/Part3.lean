/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairedBranchResidualHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalOffDiagonalTwoCycleMatching
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def
    SixVertexHorizontalPairedBranchResidualConstruction.inverseCode
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (construction : SixVertexHorizontalPairedBranchResidualConstruction
      T middle hmiddle_pos hmiddle_lt grade)
    (output : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
    {source : SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
      exists branch, construction.target source branch = output} ↪ Fin 2 where
  toFun source := finTwoEquiv.symm
    (construction.inverseBranch output source)
  inj' := by
    intro first second heq
    apply Subtype.ext
    apply construction.branch_injective
      (construction.inverseBranch output first)
    have hbranch : construction.inverseBranch output first =
        construction.inverseBranch output second := by
      apply finTwoEquiv.symm.injective
      exact heq
    calc
      construction.target first.1
          (construction.inverseBranch output first) = output :=
        construction.target_inverseBranch output first
      _ = construction.target second.1
          (construction.inverseBranch output second) :=
        (construction.target_inverseBranch output second).symm
      _ = construction.target second.1
          (construction.inverseBranch output first) := by rw [hbranch]


noncomputable def
    SixVertexHorizontalPairedBranchResidualConstruction.toAtlas
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (construction : SixVertexHorizontalPairedBranchResidualConstruction
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade where
  target := construction.target
  target_injective := construction.target_injective
  supported := construction.supported
  inverseCode := construction.inverseCode


noncomputable def
    sixVertexHorizontalPairedBranchResidualConstructionOfIsEmpty
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (hempty : IsEmpty
      (SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle)) :
    SixVertexHorizontalPairedBranchResidualConstruction T middle
      hmiddle_pos hmiddle_lt grade where
  target source := isEmptyElim source
  target_injective source := isEmptyElim source
  branch_injective branch source := isEmptyElim source
  supported source := isEmptyElim source


def SixVertexHorizontalPairedBranchResidualRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle)
    (target : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) : Prop :=
  exists branch, atlas.target source branch = target


def SixVertexHorizontalPairedBranchResidualAtlas.sourceCertificates
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
    Fin 2 ↪
      {target : SixVertexHorizontalActualSurplusTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
        SixVertexHorizontalPairedBranchResidualRelated
          atlas source target} where
  toFun branch :=
    ⟨atlas.target source (finTwoEquiv branch), ⟨finTwoEquiv branch, rfl⟩⟩
  inj' := by
    intro first second heq
    apply finTwoEquiv.injective
    apply atlas.target_injective source
    exact congrArg (fun target => target.1) heq

end
end StatMech.FrontierD
