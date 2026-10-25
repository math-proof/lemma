/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryScaledDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareScaledDomain.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part8
import Theorem.StatisticalMechanics.Code.Universality.FiniteHolomorphicInterpolation


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

def fkIsingSquareBoundaryPerturbedDobrushinDomain
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh) :
    FKIsingDobrushinDomain (fkIsingSquareBoundaryDeletedPlanar n)
      (FKIsingSquareWiredCarrier n) where
  wiredArc := fkIsingSquareWiredArc n
  markedA := fkIsingSquareMarkedA n
  markedB := fkIsingSquareMarkedB n
  markedA_mem := fkIsingSquareMarkedA_mem_wiredArc n
  markedB_mem := fkIsingSquareMarkedB_mem_wiredArc n
  sourceEdge := .source
  terminalEdge := .terminal
  medialPosition := fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh
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
