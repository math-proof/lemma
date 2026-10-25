/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.brtrouteclose
import Theorem.StatisticalMechanics.Code.Walls.btrtrifnotion.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bcr_path_crosses_box (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d) {u v : Site d}
    (p : (openSubgraph d ω).Walk u v)
    (hcut : ¬ (bc67_contractedLattice ω L x).Reachable u v) :
    ∃ w ∈ p.support, w ∈ bc61_boxAround d L x := by
  by_contra h
  push_neg at h
  exact hcut (brt_reachable_of_avoidWalk ω L x p h)


theorem bcr_boxRep_of_fullConn_cut (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d)
    {u v : Site d}
    (hconn : (openSubgraph d ω).Reachable u v)
    (hcut : ¬ (bc67_contractedLattice ω L x).Reachable u v) :
    ∃ r ∈ bc61_boxAround d L x,
      (openSubgraph d ω).Reachable u r ∧ (openSubgraph d ω).Reachable r v := by
  classical
  obtain ⟨p⟩ := hconn
  obtain ⟨r, hrsup, hrbox⟩ := bcr_path_crosses_box ω L x p hcut
  refine ⟨r, hrbox, (p.takeUntil r hrsup).reachable, (p.dropUntil r hrsup).reachable⟩


theorem bcr_center_reaches_arm_full (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (hgen : btr_IsGenuineCoarseTrif ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (openSubgraph d ω).Reachable y a₁ ∧ (openSubgraph d ω).Reachable y a₂ ∧
        (openSubgraph d ω).Reachable y a₃ := by
  obtain ⟨a₁, a₂, a₃, _, _, _, ⟨hcy1, hcy2, hcy3⟩, _, _⟩ := hgen
  exact ⟨a₁, a₂, a₃, hcy1, hcy2, hcy3⟩


theorem bcr_connectedRep_of_genuineCluster (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (hgen : btr_IsGenuineCoarseTrif ω L y) :
    ∃ (r : Site d) (a₁ a₂ a₃ : Site d), r ∈ bc61_boxAround d L y ∧
      (openSubgraph d ω).Reachable r y ∧
      (openSubgraph d ω).Reachable r a₁ ∧
      (openSubgraph d ω).Reachable r a₂ ∧
      (openSubgraph d ω).Reachable r a₃ := by
  obtain ⟨a₁, a₂, a₃, _, _, _, ⟨hcy1, hcy2, hcy3⟩, _, ⟨hs12, _, _⟩⟩ := hgen
  
  have h12 : (openSubgraph d ω).Reachable a₁ a₂ := hcy1.symm.trans hcy2
  
  have hcut : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ := hs12
  obtain ⟨r, hrbox, hra1, hra2⟩ := bcr_boxRep_of_fullConn_cut ω L y h12 hcut
  refine ⟨r, a₁, a₂, a₃, hrbox, ?_, hra1.symm, hra2, ?_⟩
  · 
    exact hra1.symm.trans hcy1.symm
  · 
    exact ((hra1.symm.trans hcy1.symm).trans hcy3)


theorem bcr_upperLines_not_genuineCluster (L : ℕ) (y : Site 2) :
    ¬ btr_IsGenuineCoarseTrif bc60_upperLines L y :=
  btr_bc60_not_genuineTrif L y


theorem bcr_upperLines_no_connectedRep (L : ℕ) (y : Site 2) :
    ¬ ∃ (_hgen : btr_IsGenuineCoarseTrif bc60_upperLines L y)
        (r : Site 2) (a₁ a₂ a₃ : Site 2), r ∈ bc61_boxAround 2 L y ∧
      (openSubgraph 2 bc60_upperLines).Reachable r y ∧
      (openSubgraph 2 bc60_upperLines).Reachable r a₁ ∧
      (openSubgraph 2 bc60_upperLines).Reachable r a₂ ∧
      (openSubgraph 2 bc60_upperLines).Reachable r a₃ := by
  rintro ⟨hgen, -⟩
  exact bcr_upperLines_not_genuineCluster L y hgen


theorem bcr_hroute_via_branch (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (aj x b tip : Site d)
    (hxb : (bc67_contractedLattice ω L aj).Reachable x b)
    (hbt : (bc67_contractedLattice ω L aj).Reachable b tip) :
    (bc67_contractedLattice ω L aj).Reachable x tip :=
  hxb.trans hbt


theorem bcr_center_reaches_branch_full (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y arm b : Site d}
    (hcy : (openSubgraph d ω).Reachable y arm)
    (hab : (bc67_contractedLattice ω L y).Reachable arm b) :
    (openSubgraph d ω).Reachable y b :=
  hcy.trans (hab.mono (bc67_contractedLattice_le ω L y))


end StatMech.Walls
