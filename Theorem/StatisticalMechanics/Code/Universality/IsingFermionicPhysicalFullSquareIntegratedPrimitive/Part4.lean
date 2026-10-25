/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquarePrimitive.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalGhostEnergy
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

theorem compatible (n : Nat) (hn : 0 < n) :
    FKIsingSquareFullPrimitiveCompatible n hn
      (vertexPrimitive n hn) (facePrimitive n hn) := by
  intro e
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
  · have h := coordinatePrimitive_horizontal_increment n hn u hu
    have hcu : fkIsingSquareFullRadialNodeAtCoordinate n (u.1 + 1, u.2) =
        .inr c := by simpa [hE] using hcp
    have hinc : fkIsingSquareFullHorizontalIncrement n hn u =
        fkIsingSquareInteriorRadialIncrement n hn e := by
      unfold fkIsingSquareFullHorizontalIncrement
      rw [hxu, hcu]
      simpa [x, c] using
        fkIsingSquareFullOrientedRadialIncrement_incidence n hn e
    simp only [vertexPrimitive, facePrimitive]
    change (coordinatePrimitive n hn p - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (coordinatePrimitive n hn u - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hE]
    linarith
  · have h := coordinatePrimitive_vertical_increment n hn u hu (hN ▸ hp)
    have hcu : fkIsingSquareFullRadialNodeAtCoordinate n (u.1, u.2 + 1) =
        .inr c := by simpa [hN] using hcp
    have hinc : fkIsingSquareFullVerticalIncrement n hn u =
        fkIsingSquareInteriorRadialIncrement n hn e := by
      unfold fkIsingSquareFullVerticalIncrement
      rw [hxu, hcu]
      simpa [x, c] using
        fkIsingSquareFullOrientedRadialIncrement_incidence n hn e
    simp only [vertexPrimitive, facePrimitive]
    change (coordinatePrimitive n hn p - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (coordinatePrimitive n hn u - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hN]
    linarith
  · have hW0 := congrArg Prod.fst hW
    have hW1 := congrArg Prod.snd hW
    have hu' : u = (p.1 + 1, p.2) := by
      apply Prod.ext <;> omega
    have h := coordinatePrimitive_horizontal_increment n hn p hp
    have hup : fkIsingSquareFullRadialNodeAtCoordinate n (p.1 + 1, p.2) =
        .inl x := by simpa [hu'] using hxu
    have hinc : fkIsingSquareFullHorizontalIncrement n hn p =
        -fkIsingSquareInteriorRadialIncrement n hn e := by
      unfold fkIsingSquareFullHorizontalIncrement
      rw [hcp, hup]
      simpa [x, c] using
        fkIsingSquareFullOrientedRadialIncrement_incidence_reverse n hn e
    simp only [vertexPrimitive, facePrimitive]
    change (coordinatePrimitive n hn p - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (coordinatePrimitive n hn u - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hu']
    linarith
  · have hS0 := congrArg Prod.fst hS
    have hS1 := congrArg Prod.snd hS
    have hu' : u = (p.1, p.2 + 1) := by
      apply Prod.ext <;> omega
    have h := coordinatePrimitive_vertical_increment n hn p hp (hu' ▸ hu)
    have hup : fkIsingSquareFullRadialNodeAtCoordinate n (p.1, p.2 + 1) =
        .inl x := by simpa [hu'] using hxu
    have hinc : fkIsingSquareFullVerticalIncrement n hn p =
        -fkIsingSquareInteriorRadialIncrement n hn e := by
      unfold fkIsingSquareFullVerticalIncrement
      rw [hcp, hup]
      simpa [x, c] using
        fkIsingSquareFullOrientedRadialIncrement_incidence_reverse n hn e
    simp only [vertexPrimitive, facePrimitive]
    change (coordinatePrimitive n hn p - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) -
      (coordinatePrimitive n hn u - coordinatePrimitive n hn
        (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))) = _
    rw [hu']
    linarith

theorem face_sub_vertex
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    facePrimitive n hn (fkIsingSquareFullFaceOfRadialIncidence n hn e) -
        vertexPrimitive n hn (fkIsingSquareInteriorRadialEndpoint n hn e) =
      fkIsingSquareInteriorRadialIncrement n hn e :=
  compatible n hn e


theorem vertex_le_face
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    vertexPrimitive n hn (fkIsingSquareInteriorRadialEndpoint n hn e) ≤
      facePrimitive n hn
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) := by
  have hgap := face_sub_vertex n hn e
  have hnonneg := fkIsingSquareInteriorRadialIncrement_nonneg n hn e
  linarith


theorem face_sub_vertex_nonneg
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    0 ≤ facePrimitive n hn
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) -
      vertexPrimitive n hn
        (fkIsingSquareInteriorRadialEndpoint n hn e) := by
  rw [face_sub_vertex n hn e]
  exact fkIsingSquareInteriorRadialIncrement_nonneg n hn e

@[simp] theorem markedB_base (n : Nat) (hn : 0 < n) :
    vertexPrimitive n hn (fkIsingSquareMarkedB n) = 0 := by
  simp [vertexPrimitive]

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
