/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

variable (P : PlanarZ2Subgraph) (M : Type*) [Fintype M] [DecidableEq M]


structure FKIsingDobrushinDomain where
  wiredArc : P.V -> Prop
  markedA : P.V
  markedB : P.V
  markedA_mem : wiredArc markedA
  markedB_mem : wiredArc markedB
  sourceEdge : M
  terminalEdge : M
  medialPosition : M -> Complex
  exploration : ConfigSpace (Sym2 P.V) -> List M
  source_mem : forall omega, sourceEdge ∈ exploration omega
  terminal_mem : forall omega, terminalEdge ∈ exploration omega
  winding : ConfigSpace (Sym2 P.V) -> M -> Real
  winding_terminal : forall omega, winding omega terminalEdge = 0

end
end StatMech.Universality
