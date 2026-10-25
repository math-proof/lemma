/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part17


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredCarrierPosition (n : Nat) (_hn : 0 < n) :
    FKIsingSquareWiredCarrier n → Complex
  | .dart d | .bond d =>
      (fkIsingSquareSitePosition (fkIsingSquareOrientedEdge n d.1).tail.1 +
        fkIsingSquareSitePosition (fkIsingSquareOrientedEdge n d.1).head.1) / 2
  | .source => fkIsingSquareSitePosition (fkIsingSquareMarkedA n).1 - 1 / 2
  | .terminal => fkIsingSquareSitePosition (fkIsingSquareMarkedB n).1 - 1 / 2


def fkIsingSquareWiredDobrushinDomain (n : Nat) (hn : 0 < n) :
    FKIsingDobrushinDomain (fkSquareBoxPlanar n)
      (FKIsingSquareWiredCarrier n) where
  wiredArc := fkIsingSquareWiredArc n
  markedA := fkIsingSquareMarkedA n
  markedB := fkIsingSquareMarkedB n
  markedA_mem := fkIsingSquareMarkedA_mem_wiredArc n
  markedB_mem := fkIsingSquareMarkedB_mem_wiredArc n
  sourceEdge := .source
  terminalEdge := .terminal
  medialPosition := fkIsingSquareWiredCarrierPosition n hn
  exploration := fkIsingSquareWiredExplorationTrace n hn
  source_mem := by
    intro omega
    rw [mem_fkIsingSquareWiredExplorationTrace_iff]
  terminal_mem := by
    intro omega
    rw [mem_fkIsingSquareWiredExplorationTrace_iff]
    exact fkIsingSquareWiredLoopGraph_source_reachable_terminal n hn omega
  winding := fkIsingSquareWiredLiftedWinding n hn
  winding_terminal := fkIsingSquareWiredLiftedWinding_terminal n hn

end
end StatMech.Universality
