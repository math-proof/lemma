/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundary.Part2


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

theorem terminalAdjacentFace_fixedBoundary (n : Nat) (hn : 0 < n) :
    fkIsingSquareFullFaceFixedBoundary n
      (terminalAdjacentFace n hn) := by
  right
  right
  have hkey' : fkIsingSquareInteriorCellKey n
      (terminalAdjacentFace n hn) =
        (-(n : Int), (n : Int) - 1) := by
    rw [show terminalAdjacentFace n hn =
      fkIsingSquareFullFaceOfRadialIncidence n hn
        (terminalAdjacentIncidence n hn) from rfl,
      fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareLeftVerticalEdge n hn
        ⟨2 * n - 1, by omega⟩, .east) = _
    simp [fkIsingSquareWedgeFaceKey, fkIsingSquareLeftVerticalEdge,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    omega
  have hsecond := congrArg Prod.snd hkey'
  simp [fkIsingSquareInteriorCellKey] at hsecond
  omega

theorem terminalAdjacentFace_le_one (n : Nat) (hn : 0 < n) :
    facePrimitive n hn (terminalAdjacentFace n hn) ≤ 1 := by
  let e := terminalAdjacentIncidence n hn
  have hcompat := face_sub_vertex n hn e
  have hend : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareMarkedB n := by
    change fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn
          ⟨2 * n - 1, by omega⟩, .east) = _
    unfold fkIsingSquareDartEndpoint
    simp only [fkIsingSquareSideCorner]
    change (fkIsingSquareOrientedEdge n
      (fkIsingSquareLeftVerticalEdge n hn
        ⟨2 * n - 1, by omega⟩)).head = _
    unfold fkIsingSquareLeftVerticalEdge
    rw [fkIsingSquareOrientedEdge_directionEdge]
    change fkIsingSquareLeftVerticalUpper n hn
      ⟨2 * n - 1, by omega⟩ = _
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [fkIsingSquareLeftVerticalUpper,
        fkIsingSquareMarkedB] <;> omega
  rw [hend, markedB_base, sub_zero] at hcompat
  rw [show terminalAdjacentFace n hn =
      fkIsingSquareFullFaceOfRadialIncidence n hn e from rfl,
    hcompat]
  change fkIsingSquareWiredPrimitiveIncrement n hn
    (.dart (leftInteriorEastDart n hn
      ⟨2 * n - 1, by omega⟩).1) ≤ 1
  exact fkIsingSquareWiredPrimitiveIncrement_le_one n hn _

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
