/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


noncomputable def clusterOpenToBarrierHom (o : Site 2) :
    (openSubgraph 2 ω).induce (cluster 2 ω o) →g latticeMinusBarrier (cluster 2 ω o) where
  toFun v := (v : Site 2)
  map_rel' := by
    intro a b hab
    have hopen : IsOpenEdge 2 ω (a : Site 2) (b : Site 2) := hab
    exact latticeMinusBarrier_adj_of_both_mem _ hopen.1 a.2 b.2


end Lattice
end StatMech
