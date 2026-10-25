/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part11


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareCornerSide_sideCorner
    (side : FKIsingMedialSide) :
    fkIsingSquareCornerSide (fkIsingSquareSideCorner side) = side := by
  cases side <;> rfl

@[simp] theorem fkIsingSquareSideCorner_cornerSide
    (corner : FKIsingSquareEdgeEndpoint × FKIsingSquareCornerTurn) :
    fkIsingSquareSideCorner (fkIsingSquareCornerSide corner) = corner := by
  rcases corner with ⟨endpoint, turn⟩
  cases endpoint <;> cases turn <;> rfl


end
end StatMech.Universality
