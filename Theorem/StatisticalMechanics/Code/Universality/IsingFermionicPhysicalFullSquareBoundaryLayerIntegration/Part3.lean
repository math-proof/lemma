/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareFullCoordinateOneFormOf_face_sub_vertex
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (hinc : forall C : FKIsingSquareInteriorRadialCell n,
      inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .east) =
        inc (fkIsingSquareInteriorRadialCellIncidence n hn C .south) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north))
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    let A := fkIsingSquareFullCoordinateOneFormOf n hn inc hinc
    A.facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) -
        A.vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) =
      inc e := by
  let A := fkIsingSquareFullCoordinateOneFormOf n hn inc hinc
  let x := fkIsingSquareInteriorRadialEndpoint n hn e
  let c := fkIsingSquareFullFaceOfRadialIncidence n hn e
  let u := fkIsingSquareFullVertexCoordinate n x
  let p := fkIsingSquareFullFaceCoordinate n c
  have hu : FKIsingSquareFullDiamond n u := by
    simpa [u, x, fkIsingSquareFullRadialNodeCoordinate] using
      fkIsingSquareFullRadialNodeCoordinate_mem_diamond n
        (Sum.inl x : FKIsingSquareFullRadialNode n)
  have hp : FKIsingSquareFullDiamond n p := by
    simpa [p, c, fkIsingSquareFullRadialNodeCoordinate] using
      fkIsingSquareFullRadialNodeCoordinate_mem_diamond n
        (Sum.inr c : FKIsingSquareFullRadialNode n)
  have hxu := fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n u hu x rfl
  have hcp := fkIsingSquareFullRadialNodeAtCoordinate_eq_face n p hp c rfl
  have hadj := fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e
  change p = (u.1 + 1, u.2) ∨ p = (u.1, u.2 + 1) ∨
      p = (u.1 - 1, u.2) ∨ p = (u.1, u.2 - 1) at hadj
  rcases hadj with hE | hN | hW | hS
  · have h := A.coordinatePrimitive_horizontal_increment u hu
    have hcu : fkIsingSquareFullRadialNodeAtCoordinate n (u.1 + 1, u.2) =
        .inr c := by simpa [hE] using hcp
    have hgap : A.horizontal u = inc e := by
      change fkIsingSquareFullHorizontalIncrementOf n hn inc u = inc e
      unfold fkIsingSquareFullHorizontalIncrementOf
      rw [hxu, hcu]
      exact fkIsingSquareFullOrientedRadialIncrementOf_incidence n hn inc e
    simp only [FKIsingSquareFullCoordinateOneForm.vertexPrimitive,
      FKIsingSquareFullCoordinateOneForm.facePrimitive]
    change (A.coordinatePrimitive p - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (A.coordinatePrimitive u - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hE]
    linarith
  · have h := A.coordinatePrimitive_vertical_increment u hu (hN ▸ hp)
    have hcu : fkIsingSquareFullRadialNodeAtCoordinate n (u.1, u.2 + 1) =
        .inr c := by simpa [hN] using hcp
    have hgap : A.vertical u = inc e := by
      change fkIsingSquareFullVerticalIncrementOf n hn inc u = inc e
      unfold fkIsingSquareFullVerticalIncrementOf
      rw [hxu, hcu]
      exact fkIsingSquareFullOrientedRadialIncrementOf_incidence n hn inc e
    simp only [FKIsingSquareFullCoordinateOneForm.vertexPrimitive,
      FKIsingSquareFullCoordinateOneForm.facePrimitive]
    change (A.coordinatePrimitive p - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (A.coordinatePrimitive u - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hN]
    linarith
  · have hW0 := congrArg Prod.fst hW
    have hW1 := congrArg Prod.snd hW
    have hu' : u = (p.1 + 1, p.2) := by
      apply Prod.ext <;> omega
    have h := A.coordinatePrimitive_horizontal_increment p hp
    have hup : fkIsingSquareFullRadialNodeAtCoordinate n (p.1 + 1, p.2) =
        .inl x := by simpa [hu'] using hxu
    have hgap : A.horizontal p = -inc e := by
      change fkIsingSquareFullHorizontalIncrementOf n hn inc p = -inc e
      unfold fkIsingSquareFullHorizontalIncrementOf
      rw [hcp, hup]
      exact fkIsingSquareFullOrientedRadialIncrementOf_incidence_reverse
        n hn inc e
    simp only [FKIsingSquareFullCoordinateOneForm.vertexPrimitive,
      FKIsingSquareFullCoordinateOneForm.facePrimitive]
    change (A.coordinatePrimitive p - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (A.coordinatePrimitive u - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hu']
    linarith
  · have hS0 := congrArg Prod.fst hS
    have hS1 := congrArg Prod.snd hS
    have hu' : u = (p.1, p.2 + 1) := by
      apply Prod.ext <;> omega
    have h := A.coordinatePrimitive_vertical_increment p hp (hu' ▸ hu)
    have hup : fkIsingSquareFullRadialNodeAtCoordinate n (p.1, p.2 + 1) =
        .inl x := by simpa [hu'] using hxu
    have hgap : A.vertical p = -inc e := by
      change fkIsingSquareFullVerticalIncrementOf n hn inc p = -inc e
      unfold fkIsingSquareFullVerticalIncrementOf
      rw [hcp, hup]
      exact fkIsingSquareFullOrientedRadialIncrementOf_incidence_reverse
        n hn inc e
    simp only [FKIsingSquareFullCoordinateOneForm.vertexPrimitive,
      FKIsingSquareFullCoordinateOneForm.facePrimitive]
    change (A.coordinatePrimitive p - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (A.coordinatePrimitive u - A.coordinatePrimitive
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hu']
    linarith

theorem fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn e) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareInteriorRadialEndpoint n hn e) =
      fkIsingSquareBoundaryLayerRadialIncrement n hn e := by
  exact fkIsingSquareFullCoordinateOneFormOf_face_sub_vertex n hn
    (fkIsingSquareBoundaryLayerRadialIncrement n hn)
    (fkIsingSquareBoundaryLayerRadialCell_increment_closed n hn) e

theorem fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareInteriorRadialEndpoint n hn e) <=
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) := by
  have hgap := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn e
  have hnonneg := fkIsingSquareBoundaryLayerRadialIncrement_nonneg n hn e
  linarith

theorem fkIsingSquareBoundaryLayerRadialIncrement_perimeterInterior
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareBoundaryLayerRadialIncrement n hn
        (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k) =
      fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
  change Complex.normSq
      ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterInteriorSide side))) = _
  rw [<- fkIsingSquareBoundaryLayerInwardSide_eq_interiorSide]
  rfl


theorem fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_face_sub_vertex
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn
            (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareBoundaryVertex n (side, k)) =
      fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
  rw [<- fkIsingSquarePerimeterInteriorRadialEndpoint n hn side k,
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex,
    fkIsingSquareBoundaryLayerRadialIncrement_perimeterInterior]

theorem fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_vertex_le_face
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareBoundaryVertex n (side, k)) <=
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareFullFaceOfRadialIncidence n hn
          (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) := by
  have hgap :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_face_sub_vertex
      n hn side k
  have hnonneg := fkIsingSquareBoundaryLayerInwardIncrement_nonneg
    n hn side k
  linarith

end
end StatMech.Universality
