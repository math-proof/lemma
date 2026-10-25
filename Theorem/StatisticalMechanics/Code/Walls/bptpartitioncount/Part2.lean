/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bsdsepdegree
import Theorem.StatisticalMechanics.Code.Walls.bc69count.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkgclassicalforest.Part2
import Def.StatisticalMechanics.Code.Walls.bptpartitioncount.Part2
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


theorem bpt_cut_ground_sets_differ (L : ℕ) (hL : 1 ≤ L) :
    (bc57_pt ((L : ℤ) + 1) 1) ∉ bc61_boxAround 2 L (0 : Site 2) ∧
    (bc57_pt ((L : ℤ) + 1) 1) ∈ bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0) := by
  constructor
  · 
    rw [bc61_mem_boxAround_zero, mem_box]; push_neg
    refine ⟨0, ?_⟩
    change ((bc57_pt ((L : ℤ) + 1) 1) 0).natAbs > L
    rw [bc57_pt_fst]; omega
  · 
    rw [bc61_mem_boxAround, mem_box]
    intro i; fin_cases i
    · change ((bc57_pt ((L : ℤ) + 1) 1 - bc57_pt (2 * (L : ℤ) + 1) 0) 0).natAbs ≤ L
      rw [Pi.sub_apply, bc57_pt_fst, bc57_pt_fst]; omega
    · change ((bc57_pt ((L : ℤ) + 1) 1 - bc57_pt (2 * (L : ℤ) + 1) 0) 1).natAbs ≤ L
      rw [Pi.sub_apply, bc57_pt_snd, bc57_pt_snd]; omega


theorem bpt_collapse_survives (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bsd_collapse_survives L


theorem bpt_partitionForest_iff_bc69 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R :=
  bfa_classical_iff_bc69 ω L R


theorem bpt_count_of_partitionForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bkg_ClassicalForestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bfa_datum_implies_count ω L R h


theorem bpt_bk_of_partitionForest (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  (bkg_bk_uniqueness_of_classical p hp1 hp0 hdata).2.1


theorem bpt_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (x : Site d) (arm : Fin 3 → Site d),
      (∀ i, arm i ∈ box d R) → (∀ i, arm i ≠ x) →
      (∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite) →
      (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) →
      ∃ t : Fin 3 → Site d,
        (∀ i, t i ∈ bpt_boundaryClass ω L R x (t i)) ∧
        (∀ i j, i ≠ j →
          Disjoint (bpt_boundaryClass ω L R x (t i)) (bpt_boundaryClass ω L R x (t j)))) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (x a b : Site d),
      bpt_boundaryClass ω L R x a = bpt_boundaryClass ω L R x b ∨
        Disjoint (bpt_boundaryClass ω L R x a) (bpt_boundaryClass ω L R x b)) ∧
    
    (∀ (L : ℕ), 1 ≤ L →
      (bc57_pt ((L : ℤ) + 1) 1) ∉ bc61_boxAround 2 L (0 : Site 2) ∧
      (bc57_pt ((L : ℤ) + 1) 1) ∈ bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      (bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R) ∧
      (bkg_ClassicalForestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L R hR x arm harmbox harmne harminf harmsep
    exact bpt_trif_three_classes_disjoint ω L R hR arm harmbox harmne harminf harmsep
  · intro ω L R x a b
    exact bpt_sameTrif_classes_laminar ω L R x a b
  · intro L hL
    exact bpt_cut_ground_sets_differ L hL
  · intro ω L R
    exact ⟨bpt_partitionForest_iff_bc69 ω L R, bpt_count_of_partitionForest ω L R⟩

end StatMech.Walls
