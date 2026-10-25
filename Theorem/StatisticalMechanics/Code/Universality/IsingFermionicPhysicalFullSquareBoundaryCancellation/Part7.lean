/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part7


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquarePerimeterMarkedCut_bottom_first
    (n : Nat) (hn : 0 < n) :
    fkIsingSquarePerimeterMarkedCut n .bottom
      (fkIsingSquarePerimeterFirstIndex n hn) := by
  exact Or.inl ⟨rfl, rfl⟩

@[simp] theorem fkIsingSquarePerimeterMarkedCut_top_last
    (n : Nat) (hn : 0 < n) :
    fkIsingSquarePerimeterMarkedCut n .top
      (fkIsingSquarePerimeterLastIndex n hn) := by
  right
  constructor
  · rfl
  · simp [fkIsingSquarePerimeterLastIndex]
    omega

theorem fkIsingSquareWiredSourceDart_eq_perimeter_bottom_first
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredSourceDart n hn =
      (fkIsingSquarePerimeterEdge n .bottom
        (fkIsingSquarePerimeterFirstIndex n hn), .south) := by
  apply Prod.ext
  · apply Subtype.ext
    change s(fkIsingSquareMarkedA n,
        fkIsingSquareNeighbor n (fkIsingSquareMarkedA n) .east
          (fkIsingSquareMarkedA_east_available n hn)) =
      s(fkIsingSquareBoundaryVertex n
          (.bottom, fkIsingSquarePerimeterFirstIndex n hn),
        fkIsingSquareNeighbor n
          (fkIsingSquareBoundaryVertex n
            (.bottom, fkIsingSquarePerimeterFirstIndex n hn)) .east
          (fkIsingSquarePerimeterDirection_available n .bottom
            (fkIsingSquarePerimeterFirstIndex n hn)))
    simp [fkIsingSquarePerimeterFirstIndex, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareMarkedA]
  · rfl

theorem fkIsingSquareWiredTerminalDart_eq_perimeter_top_last
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredTerminalDart n hn =
      (fkIsingSquarePerimeterEdge n .top
        (fkIsingSquarePerimeterLastIndex n hn), .west) := by
  apply Prod.ext
  · apply Subtype.ext
    simp only [fkIsingSquareWiredTerminalDart,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDirectionEdge]
    change s(fkIsingSquareMarkedB n,
        fkIsingSquareNeighbor n (fkIsingSquareMarkedB n) .east
          (fkIsingSquareMarkedB_east_available n hn)) =
      s(fkIsingSquareBoundaryVertex n
          (.top, fkIsingSquarePerimeterLastIndex n hn),
        fkIsingSquareNeighbor n
          (fkIsingSquareBoundaryVertex n
            (.top, fkIsingSquarePerimeterLastIndex n hn)) .west
          (fkIsingSquarePerimeterDirection_available n .top
            (fkIsingSquarePerimeterLastIndex n hn)))
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;>
      funext i <;>
      fin_cases i <;>
      simp [fkIsingSquarePerimeterLastIndex,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareMarkedB] <;> omega
  · rfl

theorem fkIsingSquareWired_top_marked_cancelled_observable
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .top
        (fkIsingSquarePerimeterLastIndex n hn),
        fkIsingSquarePerimeterCancelledSide .top)) = 1 := by
  simp only [fkIsingSquarePerimeterCancelledSide]
  rw [← fkIsingSquareWiredTerminalDart_eq_perimeter_top_last]
  exact fkIsingSquareWired_terminalDart_observable n hn

end
end StatMech.Universality
