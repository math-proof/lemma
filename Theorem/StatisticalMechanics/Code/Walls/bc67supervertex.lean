/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc66assembly
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc67supervertex
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc67_contractedLattice_adj (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d) :
    (bc67_contractedLattice ω L y).Adj a b ↔
      (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Adj a b :=
  Iff.rfl


theorem bc67_Gn_deletion_eq_removeSites (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d) :
    (bc67_contractedLattice ω L y).Reachable a b ↔
      Connected d (removeSites (bc61_boxAround d L y) ω) a b :=
  Iff.rfl


theorem bc67_contractedLattice_le (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    bc67_contractedLattice ω L y ≤ openSubgraph d ω :=
  openSubgraph_mono (bc61_removeBox_le d L y ω)


theorem bc67_connected_of_Gn {ω : ConfigSpace (Sym2 (Site d))} {L : ℕ} {y a b : Site d}
    (h : (bc67_contractedLattice ω L y).Reachable a b) : Connected d ω a b :=
  bc61_connected_of_cut ((bc67_Gn_deletion_eq_removeSites ω L y a b).mp h)


end StatMech.Walls
