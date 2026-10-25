/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicGraph.connectedWithinSet
    (P : PeriodicGraph V) (A : Set V) (x y : V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ l : List V,
    List.IsChain (P.openSubgraph omega).Adj (x :: l) ∧
    (x :: l).getLast (List.cons_ne_nil _ _) = y ∧
    ∀ v ∈ x :: l, v ∈ A}

end StatMech.FK.PeriodicPlanar
