/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCoefficientAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientInduction.Part2
import Abbrev.StatisticalMechanics.Code.Onsager.DecorationCoefficientAssembly


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising


structure ons_DecoratedEdgeSplit
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (D : ons_DecoratedContainingEdge L d) where
  cycle : (ons_decGraph L).Walk d d
  remainder : ons_DecoratedEvenSubgraph L
  cycle_isCycle : cycle.IsCycle
  cycle_snd : cycle.snd = ons_dartRev L d
  edge_split : D.1.1 = cycle.edges.toFinset ∪ remainder.1
  edge_disjoint : Disjoint cycle.edges.toFinset remainder.1
  remainder_zero : ∀ v ∈ cycle.support, incCount remainder.1 v = 0
  remainder_zero_root : incCount remainder.1 d = 0
  remainder_zero_rev : incCount remainder.1 (ons_dartRev L d) = 0

end StatMech.Onsager
