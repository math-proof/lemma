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
import Def.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem aed_sameComponent_of_commonLeaf (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {u v w : Site d} (hu : Connected d (removeSites T ω) u w)
    (hv : Connected d (removeSites T ω) v w) :
    aed_sameGlobalComponent T ω u v :=
  hu.trans hv.symm


theorem aed_globalCutArmEnds_disjoint_of_distinct (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {u v : Site d}
    (hdis : ¬ aed_sameGlobalComponent T ω u v) :
    Disjoint (daep_globalCutArmEnds T ω n u) (daep_globalCutArmEnds T ω n v) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [daep_mem_globalCutArmEnds] at hw1 hw2
  exact hdis (aed_sameComponent_of_commonLeaf T ω hw1.2 hw2.2)


theorem aed_hall_of_distinctComponents (T' : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (T : Finset (Site d)) (b : Site d → Site d)
    (hne : ∀ x ∈ T, (daep_globalCutArmEnds T' ω n (b x)).Nonempty)
    (hdistinct : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      ¬ aed_sameGlobalComponent T' ω (b x) (b y)) :
    ∀ S : Finset (Site d), S ⊆ T →
      S.card ≤ (S.biUnion (fun x => daep_globalCutArmEnds T' ω n (b x))).card :=
  bhs_hall_of_pairwiseDisjoint T (fun x => daep_globalCutArmEnds T' ω n (b x)) hne
    (fun x hx y hy hxy =>
      aed_globalCutArmEnds_disjoint_of_distinct T' ω n (hdistinct x hx y hy hxy))


end Percolation
end StatMech
