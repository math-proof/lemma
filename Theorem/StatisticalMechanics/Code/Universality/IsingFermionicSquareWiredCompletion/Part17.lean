/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part18


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWired_closed_west_south_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .west)) - Real.pi / 2 := by
  simp only [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount,
    fkIsingSquareWired_closed_west_south_rawTurnCount n hn omega e h]
  push_cast
  ring

theorem fkIsingSquareWired_closed_east_north_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .east)) - Real.pi / 2 := by
  simp only [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount,
    fkIsingSquareWired_closed_east_north_rawTurnCount n hn omega e h]
  push_cast
  ring

theorem fkIsingSquareWired_open_west_north_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .west)) + Real.pi / 2 := by
  simp only [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount,
    fkIsingSquareWired_open_west_north_rawTurnCount n hn omega e h]
  push_cast
  ring

theorem fkIsingSquareWired_open_east_south_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .east)) + Real.pi / 2 := by
  simp only [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount,
    fkIsingSquareWired_open_east_south_rawTurnCount n hn omega e h]
  push_cast
  ring

@[simp] theorem fkIsingSquareWiredLiftedWinding_terminal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    fkIsingSquareWiredLiftedWinding n hn omega .terminal = 0 := by
  simp [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount]

end
end StatMech.Universality
