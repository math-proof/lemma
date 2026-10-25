/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part14


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWired_localMate_infix_explorationOrder
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (h : fkIsingSquareWiredPathUsesLocalSide n hn omega e side) :
    [(.dart (e, side) : FKIsingSquareWiredCarrier n),
        .dart (FKIsingMedialDart.localMate omega (e, side))] <:+:
        fkIsingSquareWiredExplorationOrder n hn omega ∨
      [(.dart (FKIsingMedialDart.localMate omega (e, side)) :
          FKIsingSquareWiredCarrier n), .dart (e, side)] <:+:
        fkIsingSquareWiredExplorationOrder n hn omega := by
  have hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj
      (.dart (e, side))
      (.dart (FKIsingMedialDart.localMate omega (e, side))) := Or.inr rfl
  apply Walk.infix_support_iff_mem_edges.mpr
  apply fkIsingSquareWiredExplorationPath_mem_edges_of_adj n hn omega h hadj

@[simp] theorem fkIsingSquareWiredExplorationOrder_source_mem
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (.source : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn omega := by
  simp [fkIsingSquareWiredExplorationOrder,
    fkIsingSquareWiredExplorationPath]

@[simp] theorem fkIsingSquareWiredExplorationOrder_terminal_mem
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (.terminal : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn omega := by
  simp [fkIsingSquareWiredExplorationOrder,
    fkIsingSquareWiredExplorationPath]


end
end StatMech.Universality
