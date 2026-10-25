/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneMerge.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation
open Filter MeasureTheory Set SimpleGraph Topology Finset
open scoped ENNReal BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice StatMech.FrontierA

variable {V : Type*} [Countable V] [DecidableEq V]


def PeriodicGraph.IsTrifurcation (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (x : V) : Prop :=
  ∃ a1 a2 a3 : V,
    (P.openSubgraph omega).Adj x a1 ∧
    (P.openSubgraph omega).Adj x a2 ∧
    (P.openSubgraph omega).Adj x a3 ∧
    (P.cluster (removeVertex x omega) a1).Infinite ∧
    (P.cluster (removeVertex x omega) a2).Infinite ∧
    (P.cluster (removeVertex x omega) a3).Infinite ∧
    ¬ (P.openSubgraph (removeVertex x omega)).Reachable a1 a2 ∧
    ¬ (P.openSubgraph (removeVertex x omega)).Reachable a1 a3 ∧
    ¬ (P.openSubgraph (removeVertex x omega)).Reachable a2 a3

end StatMech.FK.PeriodicPlanar
