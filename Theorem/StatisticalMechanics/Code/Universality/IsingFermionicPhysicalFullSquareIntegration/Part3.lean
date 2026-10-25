/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates
    (n : Nat) (hn : 0 < n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamondCell n q)
    (heven : Even (q.1 + q.2)) (s : FKIsingMedialSide) :
    fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn
        (fkIsingSquareInteriorRadialCellIncidence n hn
          (fkIsingSquareFullRadialCellOfCoordinate n q hq) s) =
        (match s with
        | .west | .south => q
        | .east | .north => (q.1 + 1, q.2 + 1)) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn
        (fkIsingSquareInteriorRadialCellIncidence n hn
          (fkIsingSquareFullRadialCellOfCoordinate n q hq) s) =
        (match s with
        | .west | .north => (q.1 + 1, q.2)
        | .east | .south => (q.1, q.2 + 1)) := by
  classical
  let a : Int := Classical.choose heven
  have ha : q.1 + q.2 = a + a := Classical.choose_spec heven
  let b : Int := q.1 - a
  have h00 := hq.1
  have h10 := hq.2.1
  have h01 := hq.2.2.1
  have h11 := hq.2.2.2
  simp [FKIsingSquareFullDiamond] at h00 h10 h01 h11
  have ha0 : -(n : Int) ≤ a := by omega
  have ha1 : a < (n : Int) := by omega
  have hb0 : -(n : Int) ≤ b := by
    dsimp [b]
    omega
  have hb1 : b ≤ (n : Int) := by
    dsimp [b]
    omega
  let u : FKIsingSquareFullVertexNode n :=
    ⟨![a, b], by
      intro k
      fin_cases k
      · exact natAbs_le_of_int_bounds ha0 ha1.le
      · exact natAbs_le_of_int_bounds hb0 hb1⟩
  have hu : fkIsingSquareDirectionAvailable n u .east := by
    change a < (n : Int)
    exact ha1
  have hcell : (fkIsingSquareFullRadialCellOfCoordinate n q hq).1 =
      fkIsingSquareDirectionEdge n u .east hu := by
    simp [fkIsingSquareFullRadialCellOfCoordinate, heven, u, b, a]
  have hend : fkIsingSquareDartEndpoint n
      ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => u
      | .head => fkIsingSquareNeighbor n u .east hu := by
    unfold fkIsingSquareDartEndpoint
    rw [hcell, fkIsingSquareOrientedEdge_directionEdge]
    cases s <;> rfl
  have hdir : fkIsingSquareDartDirection n
      ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => .east
      | .head => .west := by
    unfold fkIsingSquareDartDirection
    rw [hcell, fkIsingSquareOrientedEdge_directionEdge]
    cases s <;> rfl
  have hkey : fkIsingSquareWedgeFaceKey n
      ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
      match s with
      | .west | .north => (a, b)
      | .east | .south => (a, b - 1) := by
    rw [show fkIsingSquareWedgeFaceKey n
        ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
        (let v := fkIsingSquareDartEndpoint n
            ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s)
         match fkIsingSquareDartDirection n
              ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s),
             (fkIsingSquareSideCorner s).2 with
         | .east, .counterclockwise => (v.1 0, v.1 1)
         | .east, .clockwise => (v.1 0, v.1 1 - 1)
         | .north, .counterclockwise => (v.1 0 - 1, v.1 1)
         | .north, .clockwise => (v.1 0, v.1 1)
         | .west, .counterclockwise => (v.1 0 - 1, v.1 1 - 1)
         | .west, .clockwise => (v.1 0 - 1, v.1 1)
         | .south, .counterclockwise => (v.1 0, v.1 1 - 1)
         | .south, .clockwise => (v.1 0 - 1, v.1 1 - 1)) by rfl]
    rw [hend, hdir]
    cases s <;>
      simp [fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, u, b]
  constructor
  · unfold fkIsingSquareInteriorRadialIncidenceEndpointCoordinate
    change fkIsingSquareFullVertexCoordinate n
        (fkIsingSquareDartEndpoint n
          ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s)) = _
    rw [hend]
    cases s <;>
      apply Prod.ext <;>
      simp [fkIsingSquareFullVertexCoordinate, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, u, b] <;>
      omega
  · unfold fkIsingSquareInteriorRadialIncidenceFaceCoordinate
      fkIsingSquareFullFaceCoordinate
    rw [fkIsingSquareFullFaceOfRadialIncidence_key]
    change
      let p := fkIsingSquareWedgeFaceKey n
        ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s)
      (p.1 + p.2 + 1, p.1 - p.2) = _
    rw [hkey]
    cases s <;> apply Prod.ext <;> simp [b] <;> omega

theorem fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates
    (n : Nat) (hn : 0 < n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamondCell n q)
    (hodd : ¬ Even (q.1 + q.2)) (s : FKIsingMedialSide) :
    fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn
        (fkIsingSquareInteriorRadialCellIncidence n hn
          (fkIsingSquareFullRadialCellOfCoordinate n q hq) s) =
        (match s with
        | .west | .south => (q.1, q.2 + 1)
        | .east | .north => (q.1 + 1, q.2)) ∧
      fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn
        (fkIsingSquareInteriorRadialCellIncidence n hn
          (fkIsingSquareFullRadialCellOfCoordinate n q hq) s) =
        (match s with
        | .west | .north => q
        | .east | .south => (q.1 + 1, q.2 + 1)) := by
  classical
  have ho : Odd (q.1 + q.2) := Int.not_even_iff_odd.mp hodd
  let a : Int := Classical.choose ho
  have ha : q.1 + q.2 = 2 * a + 1 := Classical.choose_spec ho
  let b : Int := q.1 - a - 1
  have h00 := hq.1
  have h10 := hq.2.1
  have h01 := hq.2.2.1
  have h11 := hq.2.2.2
  simp [FKIsingSquareFullDiamond] at h00 h10 h01 h11
  have ha0 : -(n : Int) ≤ a + 1 := by omega
  have ha1 : a + 1 < (n : Int) := by omega
  have hb0 : -(n : Int) ≤ b := by
    dsimp [b]
    omega
  have hb1 : b < (n : Int) := by
    dsimp [b]
    omega
  let u : FKIsingSquareFullVertexNode n :=
    ⟨![a + 1, b], by
      intro k
      fin_cases k
      · exact natAbs_le_of_int_bounds ha0 ha1.le
      · exact natAbs_le_of_int_bounds hb0 hb1.le⟩
  have hu : fkIsingSquareDirectionAvailable n u .north := by
    change b < (n : Int)
    exact hb1
  have hcell : (fkIsingSquareFullRadialCellOfCoordinate n q hq).1 =
      fkIsingSquareDirectionEdge n u .north hu := by
    simp [fkIsingSquareFullRadialCellOfCoordinate, hodd, u, b, a]
  have hend : fkIsingSquareDartEndpoint n
      ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => u
      | .head => fkIsingSquareNeighbor n u .north hu := by
    unfold fkIsingSquareDartEndpoint
    rw [hcell, fkIsingSquareOrientedEdge_directionEdge]
    cases s <;> rfl
  have hdir : fkIsingSquareDartDirection n
      ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => .north
      | .head => .south := by
    unfold fkIsingSquareDartDirection
    rw [hcell, fkIsingSquareOrientedEdge_directionEdge]
    cases s <;> rfl
  have hkey : fkIsingSquareWedgeFaceKey n
      ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
      match s with
      | .west | .north => (a, b)
      | .east | .south => (a + 1, b) := by
    rw [show fkIsingSquareWedgeFaceKey n
        ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s) =
        (let v := fkIsingSquareDartEndpoint n
            ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s)
         match fkIsingSquareDartDirection n
              ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s),
             (fkIsingSquareSideCorner s).2 with
         | .east, .counterclockwise => (v.1 0, v.1 1)
         | .east, .clockwise => (v.1 0, v.1 1 - 1)
         | .north, .counterclockwise => (v.1 0 - 1, v.1 1)
         | .north, .clockwise => (v.1 0, v.1 1)
         | .west, .counterclockwise => (v.1 0 - 1, v.1 1 - 1)
         | .west, .clockwise => (v.1 0 - 1, v.1 1)
         | .south, .counterclockwise => (v.1 0, v.1 1 - 1)
         | .south, .clockwise => (v.1 0 - 1, v.1 1 - 1)) by rfl]
    rw [hend, hdir]
    cases s <;>
      simp [fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, u, b]
  constructor
  · unfold fkIsingSquareInteriorRadialIncidenceEndpointCoordinate
    change fkIsingSquareFullVertexCoordinate n
        (fkIsingSquareDartEndpoint n
          ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s)) = _
    rw [hend]
    cases s <;>
      apply Prod.ext <;>
      simp [fkIsingSquareFullVertexCoordinate, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, u, b] <;>
      omega
  · unfold fkIsingSquareInteriorRadialIncidenceFaceCoordinate
      fkIsingSquareFullFaceCoordinate
    rw [fkIsingSquareFullFaceOfRadialIncidence_key]
    change
      let p := fkIsingSquareWedgeFaceKey n
        ((fkIsingSquareFullRadialCellOfCoordinate n q hq).1, s)
      (p.1 + p.2 + 1, p.1 - p.2) = _
    rw [hkey]
    cases s <;> apply Prod.ext <;> simp [b] <;> omega


end
end StatMech.Universality
