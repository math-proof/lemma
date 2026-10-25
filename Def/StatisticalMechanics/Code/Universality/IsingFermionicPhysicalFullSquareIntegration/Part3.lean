/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def FKIsingSquareFullDiamondCell (n : Nat) (q : Int × Int) : Prop :=
  FKIsingSquareFullDiamond n q ∧
    FKIsingSquareFullDiamond n (q.1 + 1, q.2) ∧
    FKIsingSquareFullDiamond n (q.1, q.2 + 1) ∧
    FKIsingSquareFullDiamond n (q.1 + 1, q.2 + 1)


noncomputable def fkIsingSquareFullRadialCellOfCoordinate
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamondCell n q) :
    FKIsingSquareInteriorRadialCell n := by
  classical
  have h00 := hq.1
  have h10 := hq.2.1
  have h01 := hq.2.2.1
  have h11 := hq.2.2.2
  simp [FKIsingSquareFullDiamond] at h00 h10 h01 h11
  by_cases heven : Even (q.1 + q.2)
  · let a : Int := Classical.choose heven
    have ha : q.1 + q.2 = a + a := Classical.choose_spec heven
    let b : Int := q.1 - a
    have ha0 : -(n : Int) ≤ a := by omega
    have ha1 : a < (n : Int) := by omega
    have hb0 : -(n : Int) < b := by
      dsimp [b]
      omega
    have hb1 : b < (n : Int) := by
      dsimp [b]
      omega
    let u : FKIsingSquareFullVertexNode n :=
      ⟨![a, b], by
        intro k
        fin_cases k
        · exact natAbs_le_of_int_bounds ha0 ha1.le
        · exact natAbs_le_of_int_bounds hb0.le hb1.le⟩
    have hu : fkIsingSquareDirectionAvailable n u .east := by
      change a < (n : Int)
      exact ha1
    let e := fkIsingSquareDirectionEdge n u .east hu
    refine ⟨e, ?_⟩
    intro s
    unfold fkIsingSquareWedgeFaceKey fkIsingSquareDartEndpoint
      fkIsingSquareDartDirection
    rw [fkIsingSquareOrientedEdge_directionEdge]
    cases s <;>
      simp [e, u, b, fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareSideCorner, fkIsingSquareInteriorFaceKey] <;>
      omega
  · have hodd : Odd (q.1 + q.2) := Int.not_even_iff_odd.mp heven
    let a : Int := Classical.choose hodd
    have ha : q.1 + q.2 = 2 * a + 1 := Classical.choose_spec hodd
    let b : Int := q.1 - a - 1
    have ha0 : -(n : Int) ≤ a := by omega
    have ha1 : a + 1 < (n : Int) := by omega
    have ha0' : -(n : Int) ≤ a + 1 := by omega
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
        · exact natAbs_le_of_int_bounds ha0' ha1.le
        · exact natAbs_le_of_int_bounds hb0 hb1.le⟩
    have hu : fkIsingSquareDirectionAvailable n u .north := by
      change b < (n : Int)
      exact hb1
    let e := fkIsingSquareDirectionEdge n u .north hu
    refine ⟨e, ?_⟩
    intro s
    unfold fkIsingSquareWedgeFaceKey fkIsingSquareDartEndpoint
      fkIsingSquareDartDirection
    rw [fkIsingSquareOrientedEdge_directionEdge]
    cases s <;>
      simp [e, u, b, fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareSideCorner, fkIsingSquareInteriorFaceKey] <;>
      omega

def fkIsingSquareInteriorRadialIncidenceEndpointCoordinate
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) : Int × Int :=
  fkIsingSquareFullVertexCoordinate n
    (fkIsingSquareInteriorRadialEndpoint n hn e)

def fkIsingSquareInteriorRadialIncidenceFaceCoordinate
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) : Int × Int :=
  fkIsingSquareFullFaceCoordinate n
    (fkIsingSquareFullFaceOfRadialIncidence n hn e)

end
end StatMech.Universality
