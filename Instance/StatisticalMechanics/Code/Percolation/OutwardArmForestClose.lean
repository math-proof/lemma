/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafDisjointClose.Part2
import Def.StatisticalMechanics.Code.Percolation.OutwardArmForestClose.Part3
open Set SimpleGraph Finset
open scoped BigOperators

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


namespace OafTree

instance : DecidableRel E := by unfold E; intro a b; infer_instance


end OafTree
end Percolation
end StatMech
