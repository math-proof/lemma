/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.brpreproute.Part2
import Theorem.StatisticalMechanics.Code.Walls.bararmray
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Walls.benentryleg
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def ben_ClusterReconnect (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (tipj : Site d) : Prop :=
  ∀ u v : Site d,
    (openSubgraph d ω).Reachable u v →
    (cluster d (removeSites (bc61_boxAround d L tipj) ω) u).Infinite →
    (cluster d (removeSites (bc61_boxAround d L tipj) ω) v).Infinite →
    (bc67_contractedLattice ω L tipj).Reachable u v


end StatMech.Walls
