/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc36rooteddiv.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BKArmSelectorClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc28forestroot.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc35globalarm
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc36_rootedArmDivergence_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    rfp_RootedArmDivergence ω n :=
  rfp_rootedArmDivergence_of_noTrif ω n hno


end StatMech.Walls
