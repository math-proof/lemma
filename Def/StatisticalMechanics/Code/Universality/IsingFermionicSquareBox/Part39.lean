/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part41


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareSitePosition (x : Site 2) : Complex :=
  (x 0 : Real) + Complex.I * (x 1 : Real)


def fkIsingSquareCarrierPosition (n : Nat) (_hn : 0 < n) :
    FKIsingSquareMedialCarrier n -> Complex
  | .dart d =>
      (fkIsingSquareSitePosition (fkIsingSquareOrientedEdge n d.1).tail.1 +
        fkIsingSquareSitePosition (fkIsingSquareOrientedEdge n d.1).head.1) / 2
  | .source => fkIsingSquareSitePosition (fkIsingSquareMarkedA n).1 - 1 / 2
  | .terminal => fkIsingSquareSitePosition (fkIsingSquareMarkedB n).1 - 1 / 2


def fkIsingSquareDobrushinDomain (n : Nat) (hn : 0 < n) :
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
  exploration := fkIsingSquareExplorationOrder n hn
  source_mem := by
    intro omega
    simp [fkIsingSquareExplorationOrder, fkIsingSquareExplorationPath]
  terminal_mem := by
    intro omega
    simp [fkIsingSquareExplorationOrder, fkIsingSquareExplorationPath]
  winding := fkIsingSquareLiftedWinding n hn
  winding_terminal := fkIsingSquareLiftedWinding_terminal n hn

end
end StatMech.Universality
