/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExterior.Part6
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareFaithfulPathUses_setClosed
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : FKIsingSquareSwitchableEdge n e.1)
    (side : FKIsingMedialSide) :
    fkIsingSquareFaithfulPathUsesLocalSide n hn
        (setClosed e.1 omega) e side ↔
      fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 (fkIsingSquareWireConfig n omega)) e side := by
  rw [fkIsingSquareFaithfulPathUsesLocalSide,
    fkIsingSquareWireConfig_setClosed n omega e.1 he]

theorem fkIsingSquareFaithfulPathUses_setOpen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : FKIsingSquareSwitchableEdge n e.1)
    (side : FKIsingMedialSide) :
    fkIsingSquareFaithfulPathUsesLocalSide n hn
        (setOpen e.1 omega) e side ↔
      fkIsingSquarePathUsesLocalSide n hn
        (setOpen e.1 (fkIsingSquareWireConfig n omega)) e side := by
  rw [fkIsingSquareFaithfulPathUsesLocalSide,
    fkIsingSquareWireConfig_setOpen n omega e.1 he]

end
end StatMech.Universality
