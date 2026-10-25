/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part7
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part2


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareBoundaryRestrictedDobrushinDomain
    (n : Nat) (hn : 0 < n) :
    FKIsingDobrushinDomain (fkIsingSquareBoundaryDeletedPlanar n)
      (FKIsingSquareWiredCarrier n) where
  wiredArc := fkIsingSquareWiredArc n
  markedA := fkIsingSquareMarkedA n
  markedB := fkIsingSquareMarkedB n
  markedA_mem := fkIsingSquareMarkedA_mem_wiredArc n
  markedB_mem := fkIsingSquareMarkedB_mem_wiredArc n
  sourceEdge := .source
  terminalEdge := .terminal
  medialPosition := fkIsingSquareWiredCarrierPosition n hn
  exploration := fun omega =>
    fkIsingSquareWiredExplorationOrder n hn
      (fkIsingSquareClosePerimeter n omega)
  source_mem := fun omega =>
    fkIsingSquareWiredExplorationOrder_source_mem n hn _
  terminal_mem := fun omega =>
    fkIsingSquareWiredExplorationOrder_terminal_mem n hn _
  winding := fun omega =>
    fkIsingSquareWiredLiftedWinding n hn
      (fkIsingSquareClosePerimeter n omega)
  winding_terminal := fun omega =>
    fkIsingSquareWiredLiftedWinding_terminal n hn _


end
end StatMech.Universality
