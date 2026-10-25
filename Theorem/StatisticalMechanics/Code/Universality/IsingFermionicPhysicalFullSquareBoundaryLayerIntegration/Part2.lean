/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareFull_increment_closed_of
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (hinc : forall C : FKIsingSquareInteriorRadialCell n,
      inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .east) =
        inc (fkIsingSquareInteriorRadialCellIncidence n hn C .south) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north))
    (q : Int × Int) (hq : FKIsingSquareFullDiamondCell n q) :
    fkIsingSquareFullVerticalIncrementOf n hn inc q +
        fkIsingSquareFullHorizontalIncrementOf n hn inc (q.1, q.2 + 1) =
      fkIsingSquareFullHorizontalIncrementOf n hn inc q +
        fkIsingSquareFullVerticalIncrementOf n hn inc (q.1 + 1, q.2) := by
  let C := fkIsingSquareFullRadialCellOfCoordinate n q hq
  let west := fkIsingSquareInteriorRadialCellIncidence n hn C .west
  let east := fkIsingSquareInteriorRadialCellIncidence n hn C .east
  let south := fkIsingSquareInteriorRadialCellIncidence n hn C .south
  let north := fkIsingSquareInteriorRadialCellIncidence n hn C .north
  have hclosed := hinc C
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
    have hH0 : fkIsingSquareFullHorizontalIncrementOf n hn inc q = inc west := by
      simp [fkIsingSquareFullHorizontalIncrementOf, nqW, neW]
    have hH1 : fkIsingSquareFullHorizontalIncrementOf n hn inc
        (q.1, q.2 + 1) = -inc east := by
      simp [fkIsingSquareFullHorizontalIncrementOf, nnE, nneE]
    have hV0 : fkIsingSquareFullVerticalIncrementOf n hn inc q = inc south := by
      simp [fkIsingSquareFullVerticalIncrementOf, nqS, nnS]
    have hV1 : fkIsingSquareFullVerticalIncrementOf n hn inc
        (q.1 + 1, q.2) = -inc north := by
      simp [fkIsingSquareFullVerticalIncrementOf, neN, nneN]
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
    have hH0 : fkIsingSquareFullHorizontalIncrementOf n hn inc q = -inc north := by
      simp [fkIsingSquareFullHorizontalIncrementOf, nqN, neN]
    have hH1 : fkIsingSquareFullHorizontalIncrementOf n hn inc
        (q.1, q.2 + 1) = inc south := by
      simp [fkIsingSquareFullHorizontalIncrementOf, nnS, nneS]
    have hV0 : fkIsingSquareFullVerticalIncrementOf n hn inc q = -inc west := by
      simp [fkIsingSquareFullVerticalIncrementOf, nqW, nnW]
    have hV1 : fkIsingSquareFullVerticalIncrementOf n hn inc
        (q.1 + 1, q.2) = inc east := by
      simp [fkIsingSquareFullVerticalIncrementOf, neE, nneE]
    rw [hH0, hH1, hV0, hV1]
    change _ + _ = _ + _ at hclosed
    linarith


end
end StatMech.Universality
