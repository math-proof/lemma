/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoStepCount.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourWeightedConvolution
open Finset


namespace StatMech.FrontierD

def piFinFourCycleEquiv (A : Type*) :
    (Fin 4 → A) ≃ A × A × A × A where
  toFun rows := (rows 3, rows 1, rows 0, rows 2)
  invFun rows := ![rows.2.2.1, rows.2.1, rows.2.2.2, rows.1]
  left_inv rows := by
    funext i
    fin_cases i <;> rfl
  right_inv rows := by
    rcases rows with ⟨seam, opposite, middle0, middle2⟩
    rfl

def sixVertexFourCycleTupleGradeCount
    (sector : Fin 5) (totalC : Nat) : Nat :=
  ∑ rows : SixVertexRow 4 × SixVertexRow 4 ×
      SixVertexRow 4 × SixVertexRow 4,
    let vertical := (piFinFourCycleEquiv (SixVertexRow 4)).symm rows
    if sixVertexUpCount
        (vertical (svFinLast sixVertexFourByFourTorus.height_pos)) =
        sector.val then
      if sixVertexVerticalRowsTotalC
          (T := sixVertexFourByFourTorus) vertical = totalC then
        ∏ j, sixVertexHorizontalTransitionWitnessCountExecutable
          (T := sixVertexFourByFourTorus) vertical j
      else 0
    else 0

def sixVertexFourCycleRowGradeCount
    (sector : Fin 5) (totalC : Nat) : Nat :=
  ∑ seam : SixVertexRow 4,
    ∑ opposite : SixVertexRow 4,
      ∑ middle0 : SixVertexRow 4,
        ∑ middle2 : SixVertexRow 4,
          let vertical : Fin 4 → SixVertexRow 4 :=
            ![middle0, opposite, middle2, seam]
          if sixVertexUpCount seam = sector.val then
            if sixVertexVerticalRowsTotalC
                (T := sixVertexFourByFourTorus) vertical = totalC then
              ∏ j, sixVertexHorizontalTransitionWitnessCountExecutable
                (T := sixVertexFourByFourTorus) vertical j
            else 0
          else 0

end StatMech.FrontierD
