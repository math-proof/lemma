/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence.Part3
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

def fkIsingSquareFullVertexOfInt
    (n : Nat) (x y : Int)
    (hx : -(n : Int) ≤ x ∧ x ≤ n)
    (hy : -(n : Int) ≤ y ∧ y ≤ n) :
    FKIsingSquareFullVertexNode n := by
  refine ⟨![x, y], ?_⟩
  intro i
  fin_cases i
  · exact (int_natAbs_le_iff x n).2 hx
  · exact (int_natAbs_le_iff y n).2 hy


noncomputable def fkIsingSquareInteriorRadialIncidenceOfInt
    (n : Nat) (hn : 0 < n) (x y : Int)
    (hxy : -(n : Int) ≤ x ∧ x < n ∧
      -(n : Int) ≤ y ∧ y < n) :
    FKIsingSquareInteriorRadialIncidence n hn := by
  let v : FKIsingSquareFullVertexNode n :=
    fkIsingSquareFullVertexOfInt n x y
      ⟨hxy.1, le_of_lt hxy.2.1⟩
      ⟨hxy.2.2.1, le_of_lt hxy.2.2.2⟩
  have hp : fkIsingSquareInteriorFaceKey n (x, y) := by
    simpa [fkIsingSquareInteriorFaceKey] using hxy
  let c : FKIsingSquareFullFaceNode n :=
    fkIsingSquareFullFaceOfKey n (x, y) hp
  have hadj : FKIsingSquareFullRadiallyAdjacent n v c := by
    left
    simp [v, c, fkIsingSquareFullFaceCoordinate,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareFullVertexOfInt]
  exact fkIsingSquareFullIncidenceOfAdjacent n hn v c hadj

end
end StatMech.Universality
