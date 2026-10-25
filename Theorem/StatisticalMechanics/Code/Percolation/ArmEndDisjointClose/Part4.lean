/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
import Def.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem aed_distinctComponent_iff_not_setoid (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (u v : Site d) :
    ¬ aed_sameGlobalComponent T ω u v ↔ ¬ (aed_globalSetoid T ω).r u v :=
  Iff.rfl


theorem aed_hall_of_disjointLeaves (T' : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (T : Finset (Site d)) (b : Site d → Site d)
    (hne : ∀ x ∈ T, (daep_globalCutArmEnds T' ω n (b x)).Nonempty)
    (hdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      Disjoint (daep_globalCutArmEnds T' ω n (b x)) (daep_globalCutArmEnds T' ω n (b y))) :
    ∀ S : Finset (Site d), S ⊆ T →
      S.card ≤ (S.biUnion (fun x => daep_globalCutArmEnds T' ω n (b x))).card :=
  bhs_hall_of_pairwiseDisjoint T (fun x => daep_globalCutArmEnds T' ω n (b x)) hne hdisj


theorem aed_globalForestArms_of_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ForestPeel ω n) :
    aed_GlobalForestArms ω n :=
  aed_globalForestArms_of_globalCutSeparation ω n
    (daep2_globalCutSeparation_of_sameCluster ω n
      (daep2_sameClusterCutSeparation_of_singleCut ω n
        (daepf_singleCutBranchSeparation_of_privateArm ω n
          (bkfl_privateArm_of_forestPeel ω n h))))

end Percolation
end StatMech
