/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareFullRadialNodeAtCoordinate_coordinate
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    fkIsingSquareFullRadialNodeCoordinate n
        (fkIsingSquareFullRadialNodeAtCoordinate n q) = q := by
  simp [fkIsingSquareFullRadialNodeAtCoordinate, hq]

theorem fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q)
    (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexCoordinate n x = q) :
    fkIsingSquareFullRadialNodeAtCoordinate n q = .inl x := by
  apply fkIsingSquareFullRadialNodeCoordinate_injective n
  rw [fkIsingSquareFullRadialNodeAtCoordinate_coordinate n q hq]
  simpa [fkIsingSquareFullRadialNodeCoordinate] using hx.symm

theorem fkIsingSquareFullRadialNodeAtCoordinate_eq_face
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q)
    (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceCoordinate n c = q) :
    fkIsingSquareFullRadialNodeAtCoordinate n q = .inr c := by
  apply fkIsingSquareFullRadialNodeCoordinate_injective n
  rw [fkIsingSquareFullRadialNodeAtCoordinate_coordinate n q hq]
  simpa [fkIsingSquareFullRadialNodeCoordinate] using hc.symm

end
end StatMech.Universality
