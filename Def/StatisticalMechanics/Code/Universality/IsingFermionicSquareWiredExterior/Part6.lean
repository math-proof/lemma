/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExterior.Part4
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareFaithfulDobrushinDomain (n : Nat) (hn : 0 < n) :
    FKIsingDobrushinDomain (fkSquareBoxPlanar n)
      (FKIsingSquareMedialCarrier n) where
  wiredArc := fkIsingSquareWiredArc n
  markedA := fkIsingSquareMarkedA n
  markedB := fkIsingSquareMarkedB n
  markedA_mem := fkIsingSquareMarkedA_mem_wiredArc n
  markedB_mem := fkIsingSquareMarkedB_mem_wiredArc n
  sourceEdge := .source
  terminalEdge := .terminal
  medialPosition := fkIsingSquareCarrierPosition n hn
  exploration := fun omega =>
    fkIsingSquareExplorationOrder n hn (fkIsingSquareWireConfig n omega)
  source_mem := by
    intro omega
    simp [fkIsingSquareExplorationOrder, fkIsingSquareExplorationPath]
  terminal_mem := by
    intro omega
    simp [fkIsingSquareExplorationOrder, fkIsingSquareExplorationPath]
  winding := fun omega =>
    fkIsingSquareLiftedWinding n hn (fkIsingSquareWireConfig n omega)
  winding_terminal := fun omega =>
    fkIsingSquareLiftedWinding_terminal n hn
      (fkIsingSquareWireConfig n omega)


def fkIsingSquareFaithfulPathUsesLocalSide (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide) : Prop :=
  fkIsingSquarePathUsesLocalSide n hn
    (fkIsingSquareWireConfig n omega) e side

end
end StatMech.Universality
