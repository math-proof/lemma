/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part8


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

theorem fkIsingSquareWiredFullLeftCycle_ne_exterior
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    Quot.mk (Equiv.Perm.SameCycle.setoid
      (fkIsingSquareWiredBlackBoundaryPerm n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)))
        (fkIsingSquareWiredFullLeftDart n hn k) ≠
      Quot.mk _ (fkIsingSquareWiredFullExteriorBlack n) := by
  intro h
  have hcycle : (fkIsingSquareWiredBlackBoundaryPerm n hn
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).SameCycle
        (fkIsingSquareWiredFullLeftDart n hn k)
        (fkIsingSquareWiredFullExteriorBlack n) :=
    Quotient.exact h
  obtain ⟨m, hm⟩ := hcycle.exists_nat_pow_eq
  have hor := fkIsingSquareWiredFullLeftDart_pow_mem n hn k m
  rw [hm] at hor
  rcases hor with h | h
  · have hv := congrArg Subtype.val h
    simp [fkIsingSquareWiredFullExteriorBlack,
      fkIsingSquareWiredFullLeftDart] at hv
  · have hv := congrArg Subtype.val h
    simp [fkIsingSquareWiredFullExteriorBlack,
      fkIsingSquareWiredFullLeftBond] at hv

theorem fkIsingSquareWiredFullInteriorCycle_ne_left
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareInteriorCell n)
    (k : Fin (2 * n)) :
    fkIsingSquareWiredFullInteriorCycle n hn c ≠
      fkIsingSquareWiredFullLeftCycle n hn k := by
  intro h
  have hcycle : (fkIsingSquareWiredBlackBoundaryPerm n hn
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).SameCycle
        (fkIsingSquareInteriorCellBlack n c)
        (fkIsingSquareWiredFullLeftDart n hn k) :=
    Quotient.exact h
  obtain ⟨m, hm⟩ := hcycle.exists_nat_pow_eq
  have hkey := fkIsingSquareWiredBlackFaceKey_pow_of_interior n hn
    (fkIsingSquareInteriorCellBlack n c)
    (fkIsingSquareInteriorCellKey n c)
    (fkIsingSquareInteriorCellBlack_faceKey n c)
    (fkIsingSquareInteriorCellKey_interior n c) m
  rw [hm] at hkey
  simp only [fkIsingSquareWiredFullLeftDart,
    fkIsingSquareWiredBlackFaceKey, Option.some.injEq] at hkey
  apply fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn (.west k)
  rw [hkey]
  exact fkIsingSquareInteriorCellKey_interior n c

theorem fkIsingSquareWiredFullInteriorCycle_ne_exterior
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareInteriorCell n) :
    fkIsingSquareWiredFullInteriorCycle n hn c ≠
      Quot.mk _ (fkIsingSquareWiredFullExteriorBlack n) := by
  intro h
  have hcycle : (fkIsingSquareWiredBlackBoundaryPerm n hn
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).SameCycle
        (fkIsingSquareInteriorCellBlack n c)
        (fkIsingSquareWiredFullExteriorBlack n) :=
    Quotient.exact h
  obtain ⟨m, hm⟩ := hcycle.exists_nat_pow_eq
  have hkey := fkIsingSquareWiredBlackFaceKey_pow_of_interior n hn
    (fkIsingSquareInteriorCellBlack n c)
    (fkIsingSquareInteriorCellKey n c)
    (fkIsingSquareInteriorCellBlack_faceKey n c)
    (fkIsingSquareInteriorCellKey_interior n c) m
  rw [hm] at hkey
  simpa [fkIsingSquareWiredFullExteriorBlack,
    fkIsingSquareWiredBlackFaceKey] using hkey

end
end StatMech.Universality
