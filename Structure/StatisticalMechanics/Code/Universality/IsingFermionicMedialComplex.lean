/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part2
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

structure FKIsingDobrushinMedialComplex (P : PlanarZ2Subgraph) where
  bondMate : Equiv.Perm (FKIsingMedialDart P)
  bondMate_involutive : Function.Involutive bondMate
  bondMate_ne : forall d, bondMate d ≠ d
  bondMate_ne_localMate : forall omega d,
    bondMate d ≠ FKIsingMedialDart.localMate omega d
  wiredArc : P.V -> Prop
  markedA : P.V
  markedB : P.V
  markedA_mem : wiredArc markedA
  markedB_mem : wiredArc markedB
  sourceDart : FKIsingMedialDart P
  terminalDart : FKIsingMedialDart P
  medialPosition : FKIsingMedialDart P -> Complex
  baseWinding : ConfigSpace (Sym2 P.V) -> FKIsingMedialVertex P -> Real
  winding_terminal : forall omega,
    baseWinding omega terminalDart.1 + terminalDart.2.angle = 0

end
end StatMech.Universality
