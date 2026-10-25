/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Def.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem fsp_treeSelector_of_rootedArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fsp_RootedArmOrder ω n) : fsp_TreeSelector ω n := by
  obtain ⟨b, hdata, hplace⟩ := h
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  exact fsp_singleCutSep_of_armPlacement ω b (hplace x hxbox htri y hybox htriy hxy hconn)


theorem fsp_singleCut_of_rootedArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fsp_RootedArmOrder ω n) : daep2_SingleCutBranchSeparation ω n :=
  fsp_singleCut_of_treeSelector ω n (fsp_treeSelector_of_rootedArmOrder ω n h)


theorem fsp_inSomeArm_of_connected (ω : ConfigSpace (Sym2 (Site d))) {x v : Site d}
    (hxv : Connected d ω x v) (hne : x ≠ v) :
    ∃ a, (openSubgraph d ω).Adj x a ∧ Connected d (removeSite x ω) a v := by
  obtain ⟨p, hp⟩ := hxv.exists_isPath
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ a _ hadj q =>
    refine ⟨a, hadj, ?_⟩
    
    have hnodup := hp.support_nodup
    rw [Walk.support_cons] at hnodup
    have hxq : x ∉ q.support := (List.nodup_cons.mp hnodup).1
    exact pap_connected_removeSite_of_walk_avoid ω x q hxq


end Percolation
end StatMech
