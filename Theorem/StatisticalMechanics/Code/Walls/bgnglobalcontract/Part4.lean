/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bptpartitioncount.Part2
import Instance.StatisticalMechanics.Code.Walls.bgnglobalcontract
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


theorem bgn_crossing_witness :
    
    (bgn_W.Adj 0 2 ∧ bgn_W.Adj 0 3 ∧ bgn_W.Adj 0 6 ∧
      ¬ (bkg_deleteVertex bgn_W 0).Reachable 2 3 ∧
      ¬ (bkg_deleteVertex bgn_W 0).Reachable 2 6 ∧
      ¬ (bkg_deleteVertex bgn_W 0).Reachable 3 6) ∧
    
    (bgn_W.Adj 1 4 ∧ bgn_W.Adj 1 5 ∧ bgn_W.Adj 1 6 ∧
      ¬ (bkg_deleteVertex bgn_W 1).Reachable 4 5 ∧
      ¬ (bkg_deleteVertex bgn_W 1).Reachable 4 6 ∧
      ¬ (bkg_deleteVertex bgn_W 1).Reachable 5 6) ∧
    
    ((bkg_deleteVertex bgn_W 0).Reachable 1 6 ∧ (bkg_deleteVertex bgn_W 1).Reachable 0 6) ∧
    ((bkg_deleteVertex bgn_W 0).Reachable 1 4 ∧ ¬ (bkg_deleteVertex bgn_W 1).Reachable 0 4) ∧
    ((bkg_deleteVertex bgn_W 1).Reachable 0 2 ∧ ¬ (bkg_deleteVertex bgn_W 0).Reachable 1 2) := by
  
  have iso2 : ∀ z, ¬ (bkg_deleteVertex bgn_W 0).Adj 2 z := by decide
  have iso3 : ∀ z, ¬ (bkg_deleteVertex bgn_W 0).Adj 3 z := by decide
  have iso4 : ∀ z, ¬ (bkg_deleteVertex bgn_W 1).Adj 4 z := by decide
  have iso5 : ∀ z, ¬ (bkg_deleteVertex bgn_W 1).Adj 5 z := by decide
  refine ⟨⟨by decide, by decide, by decide, ?_, ?_, ?_⟩,
          ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩,
          ⟨(by decide : (bkg_deleteVertex bgn_W 0).Adj 1 6).reachable,
           (by decide : (bkg_deleteVertex bgn_W 1).Adj 0 6).reachable⟩,
          ⟨(by decide : (bkg_deleteVertex bgn_W 0).Adj 1 4).reachable, ?_⟩,
          ⟨(by decide : (bkg_deleteVertex bgn_W 1).Adj 0 2).reachable, ?_⟩⟩
  · exact fun h => absurd (bgn_reach_isolated iso2 h.symm) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso2 h.symm) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso3 h.symm) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso4 h.symm) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso4 h.symm) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso5 h.symm) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso4 h) (by decide)
  · exact fun h => absurd (bgn_reach_isolated iso2 h) (by decide)


theorem bgn_forest_iff_bc69 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R :=
  bpt_partitionForest_iff_bc69 ω L R


theorem bgn_count_of_forest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bkg_ClassicalForestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bpt_count_of_partitionForest ω L R h


theorem bgn_bk_of_forest (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bpt_bk_of_partitionForest p hp1 hp0 hdata


theorem bgn_status :
    
    (∀ (L : ℕ), 1 ≤ L →
      bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) = bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) ∧
      bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) ≠ bgn_idx L (0 : Site 2)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (u a b : Site d),
      bgn_boundaryClass ω L R u a = bgn_boundaryClass ω L R u b ∨
        Disjoint (bgn_boundaryClass ω L R u a) (bgn_boundaryClass ω L R u b)) ∧
    
    ((bkg_deleteVertex bgn_W 0).Reachable 1 6 ∧ (bkg_deleteVertex bgn_W 1).Reachable 0 6 ∧
      (bkg_deleteVertex bgn_W 0).Reachable 1 4 ∧ ¬ (bkg_deleteVertex bgn_W 1).Reachable 0 4 ∧
      (bkg_deleteVertex bgn_W 1).Reachable 0 2 ∧ ¬ (bkg_deleteVertex bgn_W 0).Reachable 1 2) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R) ∧
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨fun L hL => bgn_ground_common L hL, fun ω L R u a b => bgn_sameTrif_classes_laminar ω L R u a b,
    ?_, fun ω L R => bgn_forest_iff_bc69 ω L R, fun p hp1 hp0 hdata => bgn_bk_of_forest p hp1 hp0 hdata⟩
  obtain ⟨_, _, ⟨h6a, h6b⟩, ⟨h4, h4'⟩, ⟨h2, h2'⟩⟩ := bgn_crossing_witness
  exact ⟨h6a, h6b, h4, h4', h2, h2'⟩

end StatMech.Walls
