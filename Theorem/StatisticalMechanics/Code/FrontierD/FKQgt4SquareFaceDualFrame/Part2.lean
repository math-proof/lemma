/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualFrame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualCoordinates.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualFrame
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

open StatMech.Universality

open StatMech.FK.PeriodicPlanar

noncomputable section

@[simp] theorem fciFrameTranslation_inv_smul (x : Site 2) :
    fciFrameTranslation⁻¹ • x = phb_doubleDualShift x := by
  funext i
  rw [smul_site_apply]
  fin_cases i
  · change (-1 : Int) + x 0 = x 0 - 1
    omega
  · change (-1 : Int) + x 1 = x 1 - 1
    omega


theorem inverseFaceDualConfig_eq_shift_faceDual_of_adj
    (omega : ConfigSpace (Sym2 (Site 2)))
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y) :
    inverseFaceDualConfig omega s(x, y) =
      ConfigSpace.shift fciFrameTranslation (fci_faceDualConfig omega) s(x, y) := by
  rw [ConfigSpace.shift_apply, smul_sym2_mk,
    fciFrameTranslation_inv_smul, fciFrameTranslation_inv_smul]
  exact inverseFaceDualConfig_eq_faceDual_doubleDualShift omega hxy


theorem openSubgraph_inverseFaceDual_eq_shift_faceDual
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraph 2 (inverseFaceDualConfig omega) =
      openSubgraph 2
        (ConfigSpace.shift fciFrameTranslation (fci_faceDualConfig omega)) := by
  ext x y
  by_cases hxy : (hypercubicLattice 2).Adj x y
  · simp only [openSubgraph_adj, hxy, true_and]
    rw [inverseFaceDualConfig_eq_shift_faceDual_of_adj omega hxy]
  · simp only [openSubgraph_adj, hxy, false_and]


theorem inverseFaceDual_hasInfiniteCluster_iff_faceDual
    (omega : ConfigSpace (Sym2 (Site 2))) :
    square.HasInfiniteCluster (inverseFaceDualConfig omega) ↔
      square.HasInfiniteCluster (fci_faceDualConfig omega) := by
  change (∃ x, (cluster 2 (inverseFaceDualConfig omega) x).Infinite) ↔
    ∃ x, (cluster 2 (fci_faceDualConfig omega) x).Infinite
  have hcluster : ∀ x,
      cluster 2 (inverseFaceDualConfig omega) x =
        cluster 2 (ConfigSpace.shift fciFrameTranslation
          (fci_faceDualConfig omega)) x := by
    intro x
    unfold cluster Lattice.Connected
    rw [openSubgraph_inverseFaceDual_eq_shift_faceDual]
  constructor
  · rintro ⟨x, hx⟩
    have hxShift : (cluster 2 (ConfigSpace.shift fciFrameTranslation
        (fci_faceDualConfig omega)) x).Infinite := by
      rwa [← hcluster x]
    let y := fciFrameTranslation⁻¹ • x
    refine ⟨y, ?_⟩
    have htranslate := cluster_shift fciFrameTranslation
      (fci_faceDualConfig omega) y
    rw [smul_inv_smul] at htranslate
    rw [htranslate] at hxShift
    exact (Set.infinite_image_iff
      (Set.injOn_of_injective (smul_injective fciFrameTranslation))).mp hxShift
  · rintro ⟨x, hx⟩
    refine ⟨fciFrameTranslation • x, ?_⟩
    rw [hcluster]
    have htranslate := cluster_shift fciFrameTranslation
      (fci_faceDualConfig omega) x
    rw [htranslate]
    exact (Set.infinite_image_iff
      (Set.injOn_of_injective (smul_injective fciFrameTranslation))).mpr hx

end
end StatMech.FrontierD
