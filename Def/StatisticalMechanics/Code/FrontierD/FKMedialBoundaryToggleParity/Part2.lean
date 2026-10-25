/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity
open Equiv


namespace StatMech.FrontierD

variable {T : EvenTorus}


def fkMedialBlackSideIndex : FKMedialSide → Bool
  | .west | .south => false
  | .east | .north => true


def fkMedialBlackDartEquivVertexBool (T : EvenTorus) :
    FKMedialBlackDart T ≃ T.Vertex × Bool where
  toFun d := (d.1.1, fkMedialBlackSideIndex d.1.2)
  invFun vb := if vb.2 then fkMedialBlackDart1 vb.1 else fkMedialBlackDart0 vb.1
  left_inv d := by
    apply Subtype.ext
    rcases d with ⟨⟨v, side⟩, hd⟩
    cases side <;> by_cases hp : fkMedialVertexParity v <;>
      simp [fkMedialBlackSideIndex, fkMedialBlackDart0, fkMedialBlackDart1,
        fkMedialCheckerColor, fkMedialSideVertical, hp] at hd ⊢
  right_inv vb := by
    rcases vb with ⟨v, b⟩
    cases b <;> by_cases hp : fkMedialVertexParity v <;>
      simp [fkMedialBlackSideIndex, fkMedialBlackDart0, fkMedialBlackDart1, hp]

end StatMech.FrontierD
