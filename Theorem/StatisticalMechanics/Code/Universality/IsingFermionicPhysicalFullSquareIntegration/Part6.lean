/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part6


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareFull_increment_closed
    (n : Nat) (hn : 0 < n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamondCell n q) :
    fkIsingSquareFullVerticalIncrement n hn q +
        fkIsingSquareFullHorizontalIncrement n hn (q.1, q.2 + 1) =
      fkIsingSquareFullHorizontalIncrement n hn q +
        fkIsingSquareFullVerticalIncrement n hn (q.1 + 1, q.2) := by
  let C := fkIsingSquareFullRadialCellOfCoordinate n q hq
  let west := fkIsingSquareInteriorRadialCellIncidence n hn C .west
  let east := fkIsingSquareInteriorRadialCellIncidence n hn C .east
  let south := fkIsingSquareInteriorRadialCellIncidence n hn C .south
  let north := fkIsingSquareInteriorRadialCellIncidence n hn C .north
  have hclosed := fkIsingSquareInteriorRadialCell_increment_closed n hn C
  by_cases heven : Even (q.1 + q.2)
  · have hw := fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates
      n hn q hq heven .west
    have he := fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates
      n hn q hq heven .east
    have hs := fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates
      n hn q hq heven .south
    have hnorth := fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates
      n hn q hq heven .north
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn west = q ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn west =
        (q.1 + 1, q.2) at hw
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn east =
        (q.1 + 1, q.2 + 1) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn east =
        (q.1, q.2 + 1) at he
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn south = q ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn south =
        (q.1, q.2 + 1) at hs
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn north =
        (q.1 + 1, q.2 + 1) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn north =
        (q.1 + 1, q.2) at hnorth
    have nqW := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n q hq.1
      (fkIsingSquareInteriorRadialEndpoint n hn west) hw.1
    have neW := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
      (q.1 + 1, q.2) hq.2.1
      (fkIsingSquareFullFaceOfRadialIncidence n hn west) hw.2
    have nnE := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
      (q.1, q.2 + 1) hq.2.2.1
      (fkIsingSquareFullFaceOfRadialIncidence n hn east) he.2
    have nneE := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
      (q.1 + 1, q.2 + 1) hq.2.2.2
      (fkIsingSquareInteriorRadialEndpoint n hn east) he.1
    have nqS := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n q hq.1
      (fkIsingSquareInteriorRadialEndpoint n hn south) hs.1
    have nnS := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
      (q.1, q.2 + 1) hq.2.2.1
      (fkIsingSquareFullFaceOfRadialIncidence n hn south) hs.2
    have neN := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
      (q.1 + 1, q.2) hq.2.1
      (fkIsingSquareFullFaceOfRadialIncidence n hn north) hnorth.2
    have nneN := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
      (q.1 + 1, q.2 + 1) hq.2.2.2
      (fkIsingSquareInteriorRadialEndpoint n hn north) hnorth.1
    have hH0 : fkIsingSquareFullHorizontalIncrement n hn q =
        fkIsingSquareInteriorRadialIncrement n hn west := by
      simp [fkIsingSquareFullHorizontalIncrement, nqW, neW]
    have hH1 : fkIsingSquareFullHorizontalIncrement n hn (q.1, q.2 + 1) =
        -fkIsingSquareInteriorRadialIncrement n hn east := by
      simp [fkIsingSquareFullHorizontalIncrement, nnE, nneE]
    have hV0 : fkIsingSquareFullVerticalIncrement n hn q =
        fkIsingSquareInteriorRadialIncrement n hn south := by
      simp [fkIsingSquareFullVerticalIncrement, nqS, nnS]
    have hV1 : fkIsingSquareFullVerticalIncrement n hn (q.1 + 1, q.2) =
        -fkIsingSquareInteriorRadialIncrement n hn north := by
      simp [fkIsingSquareFullVerticalIncrement, neN, nneN]
    rw [hH0, hH1, hV0, hV1]
    change _ + _ = _ + _ at hclosed
    linarith
  · have hw := fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates
      n hn q hq heven .west
    have he := fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates
      n hn q hq heven .east
    have hs := fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates
      n hn q hq heven .south
    have hnorth := fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates
      n hn q hq heven .north
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn west =
        (q.1, q.2 + 1) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn west = q at hw
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn east =
        (q.1 + 1, q.2) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn east =
        (q.1 + 1, q.2 + 1) at he
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn south =
        (q.1, q.2 + 1) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn south =
        (q.1 + 1, q.2 + 1) at hs
    change fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn north =
        (q.1 + 1, q.2) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn north = q at hnorth
    have nnW := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
      (q.1, q.2 + 1) hq.2.2.1
      (fkIsingSquareInteriorRadialEndpoint n hn west) hw.1
    have nqW := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n q hq.1
      (fkIsingSquareFullFaceOfRadialIncidence n hn west) hw.2
    have neE := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
      (q.1 + 1, q.2) hq.2.1
      (fkIsingSquareInteriorRadialEndpoint n hn east) he.1
    have nneE := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
      (q.1 + 1, q.2 + 1) hq.2.2.2
      (fkIsingSquareFullFaceOfRadialIncidence n hn east) he.2
    have nnS := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
      (q.1, q.2 + 1) hq.2.2.1
      (fkIsingSquareInteriorRadialEndpoint n hn south) hs.1
    have nneS := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n
      (q.1 + 1, q.2 + 1) hq.2.2.2
      (fkIsingSquareFullFaceOfRadialIncidence n hn south) hs.2
    have neN := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n
      (q.1 + 1, q.2) hq.2.1
      (fkIsingSquareInteriorRadialEndpoint n hn north) hnorth.1
    have nqN := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n q hq.1
      (fkIsingSquareFullFaceOfRadialIncidence n hn north) hnorth.2
    have hH0 : fkIsingSquareFullHorizontalIncrement n hn q =
        -fkIsingSquareInteriorRadialIncrement n hn north := by
      simp [fkIsingSquareFullHorizontalIncrement, nqN, neN]
    have hH1 : fkIsingSquareFullHorizontalIncrement n hn (q.1, q.2 + 1) =
        fkIsingSquareInteriorRadialIncrement n hn south := by
      simp [fkIsingSquareFullHorizontalIncrement, nnS, nneS]
    have hV0 : fkIsingSquareFullVerticalIncrement n hn q =
        -fkIsingSquareInteriorRadialIncrement n hn west := by
      simp [fkIsingSquareFullVerticalIncrement, nqW, nnW]
    have hV1 : fkIsingSquareFullVerticalIncrement n hn (q.1 + 1, q.2) =
        fkIsingSquareInteriorRadialIncrement n hn east := by
      simp [fkIsingSquareFullVerticalIncrement, neE, nneE]
    rw [hH0, hH1, hV0, hV1]
    change _ + _ = _ + _ at hclosed
    linarith

end
end StatMech.Universality
