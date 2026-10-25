/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc35globalarm
import Theorem.StatisticalMechanics.Code.Walls.bc36rooteddiv.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc37_armAdjGraph (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    SimpleGraph {x : Site d // x ∈ tfc_trifFinset ω n} where
  Adj a b := bc37_ArmAdjacent ω n a.1 b.1
  symm := ⟨fun _ _ h => bc37_armAdjacent_symm ω n h⟩
  loopless := ⟨fun a h => bc37_armAdjacent_irrefl ω n a.1 h⟩


end StatMech.Walls
