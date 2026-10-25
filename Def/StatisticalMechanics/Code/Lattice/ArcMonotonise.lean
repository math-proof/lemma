/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcMonotonise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part9
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


def amo_proj (ω : ConfigSpace (Sym2 (Site 2))) (S : Set (Site 2)) :
    (openSubgraphInduce 2 ω S) →g (hypercubicLattice 2) where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    rw [openSubgraphInduce_adj] at huv
    exact (openSubgraph_le ω) huv


end Lattice
end StatMech
