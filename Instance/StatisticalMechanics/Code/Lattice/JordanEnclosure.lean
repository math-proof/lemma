/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

noncomputable instance instLocallyFiniteFaceBoundaryGraph (S : Set (Site 2)) :
    SimpleGraph.LocallyFinite (faceBoundaryGraph S) := by
  classical
  exact fun f =>
    Fintype.ofFinset
      ((candFinset 2 f).filter (fun g => (faceBoundaryGraph S).Adj f g)) (by
        intro g
        rw [Finset.mem_filter, SimpleGraph.mem_neighborSet]
        refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
        exact mem_candFinset_of_adj 2 f g (faceBoundaryGraph_le S h))


end Lattice
end StatMech
