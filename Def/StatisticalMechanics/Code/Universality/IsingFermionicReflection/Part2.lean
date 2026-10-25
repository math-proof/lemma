/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflection
open Filter Metric Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

def FKIsingDobrushinDomain.reflect
    {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]
    (D : FKIsingDobrushinDomain P M) : FKIsingDobrushinDomain P M where
  wiredArc := D.wiredArc
  markedA := D.markedA
  markedB := D.markedB
  markedA_mem := D.markedA_mem
  markedB_mem := D.markedB_mem
  sourceEdge := D.sourceEdge
  terminalEdge := D.terminalEdge
  medialPosition := fun e ↦ (starRingEnd Complex) (D.medialPosition e)
  exploration := D.exploration
  source_mem := D.source_mem
  terminal_mem := D.terminal_mem
  winding := D.winding
  winding_terminal := D.winding_terminal

end
end StatMech.Universality
