/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean -/

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
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem daep2_armEnds_share_forces_branch_connection (ω : ConfigSpace (Sym2 (Site d)))
    {x a b w : Site d}
    (hwa : Connected d (removeSite x ω) a w) (hwb : Connected d (removeSite x ω) b w) :
    Connected d (removeSite x ω) a b :=
  hwa.trans hwb.symm


theorem daep2_no_shared_boundary_of_disconnected_branches (ω : ConfigSpace (Sym2 (Site d)))
    {x a b : Site d} (hdis : ¬ Connected d (removeSite x ω) a b) :
    ∀ w, ¬ (Connected d (removeSite x ω) a w ∧ Connected d (removeSite x ω) b w) := by
  intro w ⟨hwa, hwb⟩
  exact hdis (daep2_armEnds_share_forces_branch_connection ω hwa hwb)


theorem daep2_globalCut_disconnected_of_omega_disconnected (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {u v : Site d} (hdis : ¬ Connected d ω u v) :
    ¬ Connected d (removeSites T ω) u v :=
  fun hc => hdis (connected_mono (daep_removeSites_le T ω) hc)


theorem daep2_crossCluster_branches_globalCut_disconnected (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {x y a b : Site d}
    (hxa : Connected d ω x a) (hyb : Connected d ω y b)
    (hxy : ¬ Connected d ω x y) :
    ¬ Connected d (removeSites T ω) a b := by
  intro hc
  
  have hab : Connected d ω a b := connected_mono (daep_removeSites_le T ω) hc
  exact hxy (hxa.trans (hab.trans hyb.symm))


theorem daep2_removeSites_le_removeSite (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} (hxT : x ∈ T) :
    removeSites T ω ≤ removeSite x ω := by
  intro e
  unfold removeSites removeSite
  by_cases hx : x ∈ e
  · 
    rw [if_pos hx, if_pos ⟨x, hxT, hx⟩]
  · 
    rw [if_neg hx]
    by_cases hT : ∃ t ∈ T, t ∈ e
    · rw [if_pos hT]; exact Bool.false_le _
    · rw [if_neg hT]


theorem daep2_globalCut_disconnected_of_singleCut (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {x u v : Site d} (hxT : x ∈ T)
    (hdis : ¬ Connected d (removeSite x ω) u v) :
    ¬ Connected d (removeSites T ω) u v :=
  fun hc => hdis (connected_mono (daep2_removeSites_le_removeSite T ω hxT) hc)


end Percolation
end StatMech
