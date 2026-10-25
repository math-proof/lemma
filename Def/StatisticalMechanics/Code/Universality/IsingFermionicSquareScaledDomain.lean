/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part3
import Theorem.StatisticalMechanics.Code.Universality.FiniteInjectivePerturbation


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredScaledDobrushinDomain
    (n : Nat) (hn : 0 < n) (mesh : Real) :
    FKIsingDobrushinDomain (fkSquareBoxPlanar n)
      (FKIsingSquareWiredCarrier n) where
  wiredArc := fkIsingSquareWiredArc n
  markedA := fkIsingSquareMarkedA n
  markedB := fkIsingSquareMarkedB n
  markedA_mem := fkIsingSquareMarkedA_mem_wiredArc n
  markedB_mem := fkIsingSquareMarkedB_mem_wiredArc n
  sourceEdge := .source
  terminalEdge := .terminal
  medialPosition := fun a ↦ (mesh : Complex) *
    fkIsingSquareWiredCarrierPosition n hn a
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
