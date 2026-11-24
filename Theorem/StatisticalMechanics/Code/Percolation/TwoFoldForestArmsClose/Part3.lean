module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeRealiseClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.TwoFoldHallClose.Part2
public import Def.StatisticalMechanics.Code.Percolation.TwoFoldForestArmsClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldForestArmsClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tffa_spanningTreeLeafCount_of_leafDisjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : tffa_LeafDisjointSelection ω n)
    (hbase : (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
    flc2_SpanningTreeLeafCount ω n :=
  str_spanningTreeLeafCount_of_forestLeafSelection ω n h hbase


theorem tffa_leafDisjoint_of_twoFoldForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : tfh_TwoFoldForestArms ω n) :
    tffa_LeafDisjointSelection ω n :=
  tfh_forestLeafSelection_of_twoFoldForestArms ω n hn h

end Percolation
end StatMech
