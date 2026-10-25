/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

theorem fkIsingSquareWiredFullInteriorCycle_injective
    (n : Nat) (hn : 0 < n) :
    Function.Injective (fkIsingSquareWiredFullInteriorCycle n hn) := by
  intro c d hcd
  have hcycle : (fkIsingSquareWiredBlackBoundaryPerm n hn
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).SameCycle
        (fkIsingSquareInteriorCellBlack n c)
        (fkIsingSquareInteriorCellBlack n d) :=
    Quotient.exact hcd
  obtain ⟨k, hk⟩ := hcycle.exists_nat_pow_eq
  have hkey := fkIsingSquareWiredBlackFaceKey_pow_of_interior n hn
    (fkIsingSquareInteriorCellBlack n c)
    (fkIsingSquareInteriorCellKey n c)
    (fkIsingSquareInteriorCellBlack_faceKey n c)
    (fkIsingSquareInteriorCellKey_interior n c) k
  rw [hk, fkIsingSquareInteriorCellBlack_faceKey] at hkey
  apply fkIsingSquareInteriorCellKey_injective n
  exact Option.some.inj hkey.symm

theorem fkIsingSquareWiredBoundaryDart_west_eq_leftEdge
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareWiredBoundaryDart n hn (.west k) =
      (fkIsingSquareLeftVerticalEdge n hn k, .west) := by
  apply Prod.ext
  · apply Subtype.ext
    change s(fkIsingSquareLeftVerticalLower n hn k,
        fkIsingSquareNeighbor n (fkIsingSquareLeftVerticalLower n hn k) .north
          (fkIsingSquareLeftVerticalLower_north_available n hn k)) =
      s(fkIsingSquareLeftVerticalUpper n hn k,
        fkIsingSquareNeighbor n (fkIsingSquareLeftVerticalUpper n hn k) .south
          (fkIsingSquareLeftVerticalUpper_south_available n hn k))
    rw [Sym2.eq_iff]
    apply Or.inr
    constructor
    · apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [fkIsingSquareWiredBoundaryDart,
          fkIsingSquareDirectionDart, fkIsingSquareLeftVerticalEdge,
          fkIsingSquareDirectionEdge, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareLeftVerticalLower,
          fkIsingSquareLeftVerticalUpper, Pi.add_apply]
    · apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [fkIsingSquareWiredBoundaryDart,
          fkIsingSquareDirectionDart, fkIsingSquareLeftVerticalEdge,
          fkIsingSquareDirectionEdge, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareLeftVerticalLower,
          fkIsingSquareLeftVerticalUpper, Pi.add_apply]
  · rfl

theorem fkIsingSquareWiredBoundaryDart_north_eq_leftEdge
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareWiredBoundaryDart n hn (.north k) =
      (fkIsingSquareLeftVerticalEdge n hn k, .north) := by
  rfl

end
end StatMech.Universality
