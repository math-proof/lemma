/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundary


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

theorem left_boundary_interior_increment_eq
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareInteriorRadialIncrement n hn
        (Quot.mk _ (leftInteriorEastDart n hn k)) =
      fkIsingSquareInteriorRadialIncrement n hn
        (Quot.mk _ (leftInteriorSouthDart n hn k)) := by
  let e := fkIsingSquareLeftVerticalEdge n hn k
  have hwestNorth :
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .west)) =
        fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .north)) := by
    let w := fkIsingSquareWiredBoundaryDart n hn (.west k)
    have hw : w = (e, .west) := by
      apply Prod.ext
      · apply Subtype.ext
        change s(fkIsingSquareLeftVerticalLower n hn k,
            fkIsingSquareNeighbor n
              (fkIsingSquareLeftVerticalLower n hn k) .north
              (fkIsingSquareLeftVerticalLower_north_available n hn k)) =
          s(fkIsingSquareLeftVerticalUpper n hn k,
            fkIsingSquareNeighbor n
              (fkIsingSquareLeftVerticalUpper n hn k) .south
              (fkIsingSquareLeftVerticalUpper_south_available n hn k))
        rw [Sym2.eq_iff]
        apply Or.inr
        constructor <;>
          apply Subtype.ext <;>
          funext i <;>
          fin_cases i <;>
          simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
            fkIsingSquareLeftVerticalLower,
            fkIsingSquareLeftVerticalUpper]
      · rfl
    have hnorth : fkIsingSquareWiredBondMate n hn w = (e, .north) := by
      rw [fkIsingSquareWiredBondMate_west]
      rfl
    have hsource : w ≠ fkIsingSquareWiredSourceDart n hn := by
      intro h
      have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
      cases hi
    have hterminal : w ≠ fkIsingSquareWiredTerminalDart n hn := by
      intro h
      have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
      cases hi
    have h := fkIsingSquareWiredPrimitiveIncrement_bondDartMate
      n hn w hsource hterminal
    rw [hnorth, hw] at h
    exact h.symm
  have hclosed :=
    fkIsingSquareWiredPrimitiveIncrement_local_closed n hn e
  change fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .east)) =
    fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .south))
  linarith

theorem wiredArc_vertex_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    vertexPrimitive n hn (fkIsingSquareLeftVerticalLower n hn k) =
      vertexPrimitive n hn (fkIsingSquareLeftVerticalUpper n hn k) := by
  let east : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (leftInteriorEastDart n hn k)
  let south : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (leftInteriorSouthDart n hn k)
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn east =
      fkIsingSquareFullFaceOfRadialIncidence n hn south := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fkIsingSquareLeftVerticalEdge n hn k, .east) =
      fkIsingSquareWedgeFaceKey n
        (fkIsingSquareLeftVerticalEdge n hn k, .south)
    simp [fkIsingSquareWedgeFaceKey, fkIsingSquareLeftVerticalEdge,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
  have h := vertex_eq_of_common_face_increment_eq n hn south east hface.symm
    (left_boundary_interior_increment_eq n hn k).symm
  change vertexPrimitive n hn
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn k, .south)) =
    vertexPrimitive n hn
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn k, .east)) at h
  simpa [fkIsingSquareLeftVerticalEdge, fkIsingSquareDartEndpoint,
    fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite, fkIsingSquareLeftVerticalLower,
    fkIsingSquareLeftVerticalUpper] using h

theorem wiredArc_lower_const
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    vertexPrimitive n hn (fkIsingSquareLeftVerticalLower n hn k) =
      vertexPrimitive n hn
        (fkIsingSquareLeftVerticalLower n hn ⟨0, by omega⟩) := by
  let P : Nat → Prop := fun j ↦ ∀ hj : j < 2 * n,
    vertexPrimitive n hn
        (fkIsingSquareLeftVerticalLower n hn ⟨j, hj⟩) =
      vertexPrimitive n hn
        (fkIsingSquareLeftVerticalLower n hn ⟨0, by omega⟩)
  have hP : ∀ j, P j := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
        intro hj
        have hstep := wiredArc_vertex_step n hn ⟨j, by omega⟩
        have heq : fkIsingSquareLeftVerticalUpper n hn ⟨j, by omega⟩ =
            fkIsingSquareLeftVerticalLower n hn ⟨j + 1, hj⟩ := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [fkIsingSquareLeftVerticalUpper,
              fkIsingSquareLeftVerticalLower] <;> ring
        rw [heq] at hstep
        exact hstep.symm.trans (ih (by omega))
  exact hP k.val k.isLt

theorem wiredArc_lower_zero
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    vertexPrimitive n hn (fkIsingSquareLeftVerticalLower n hn k) = 0 := by
  let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hlast := wiredArc_vertex_step n hn last
  have hupper : fkIsingSquareLeftVerticalUpper n hn last =
      fkIsingSquareMarkedB n := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [last, fkIsingSquareLeftVerticalUpper,
        fkIsingSquareMarkedB] <;> omega
  rw [hupper, markedB_base] at hlast
  calc
    _ = vertexPrimitive n hn
          (fkIsingSquareLeftVerticalLower n hn last) := by
        rw [wiredArc_lower_const n hn k,
          wiredArc_lower_const n hn last]
    _ = 0 := hlast

theorem vertex_fixedBoundary_eq_zero
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexFixedBoundary n x) :
    vertexPrimitive n hn x = 0 := by
  have hx0 : x.1 0 = -(n : Int) := hx
  have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
  by_cases htop : x.1 1 = (n : Int)
  · have heq : x = fkIsingSquareMarkedB n := by
      apply Subtype.ext
      funext i
      fin_cases i
      · simpa [fkIsingSquareMarkedB] using hx0
      · simpa [fkIsingSquareMarkedB] using htop
    rw [heq, markedB_base]
  · let j : Nat := (x.1 1 + (n : Int)).toNat
    have hj0 : 0 ≤ x.1 1 + (n : Int) := by omega
    have hj : j < 2 * n := by
      rw [show j = Int.toNat (x.1 1 + (n : Int)) from rfl,
        Int.toNat_lt] <;> omega
    let k : Fin (2 * n) := ⟨j, hj⟩
    have heq : x = fkIsingSquareLeftVerticalLower n hn k := by
      apply Subtype.ext
      funext i
      fin_cases i
      · simpa [k, j, fkIsingSquareLeftVerticalLower] using hx0
      · simp [k, j, fkIsingSquareLeftVerticalLower,
          Int.toNat_of_nonneg hj0]
    rw [heq, wiredArc_lower_zero]

theorem vertex_fixedBoundary_nonneg
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexFixedBoundary n x) :
    0 ≤ vertexPrimitive n hn x := by
  rw [vertex_fixedBoundary_eq_zero n hn x hx]


end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
