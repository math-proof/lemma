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
import Def.StatisticalMechanics.Code.Walls.bc37armadj.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc37_armAdjGraph_le_trifGraph (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc37_armAdjGraph ω n ≤ stt_trifGraph ω n := by
  intro a b hab
  exact ⟨fun h => hab.1 (congrArg Subtype.val h), hab.2.1⟩


theorem bc37_sameCluster_of_armAdjReachable (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {a b : {x : Site d // x ∈ tfc_trifFinset ω n}} (h : (bc37_armAdjGraph ω n).Reachable a b) :
    Connected d ω a.1 b.1 :=
  (stt_reachable_iff ω n a b).mp (h.mono (bc37_armAdjGraph_le_trifGraph ω n))


theorem bc37_isForest_iff_isAcyclic (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (bc37_armAdjGraph ω n).IsAcyclic ↔ ∀ ⦃a b⦄ (p q : (bc37_armAdjGraph ω n).Path a b), p = q :=
  SimpleGraph.isAcyclic_iff_path_unique


end StatMech.Walls
