import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bgnglobalcontract.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bgn_Gn_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean)
-/
@[path]
private lemma bgn_Gn_adj_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {j k : Site d} :
-- imply
  (bgn_Gn ω L).Adj j k ↔ j ≠ k ∧ ∃ a b : Site d, bgn_idx L a = j ∧ bgn_idx L b = k ∧ (openSubgraph d ω).Adj a b := by
-- proof
  apply StatMech.Walls.bgn_Gn_adj ω L j k

/--
[bgn_idx_adversarySite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean)
-/
@[path]
private lemma bgn_idx_adversarySite_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) = bc57_pt 1 0 := by
-- proof
  apply StatMech.Walls.bgn_idx_adversarySite L hL

/--
[bgn_idx_trifCentre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean)
-/
@[path]
private lemma bgn_idx_trifCentre_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) = bc57_pt 1 0 := by
-- proof
  apply StatMech.Walls.bgn_idx_trifCentre L hL

/--
[bgn_idx_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean)
-/
@[path]
private lemma bgn_idx_origin_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  bgn_idx L (0 : Site 2) = bc57_pt 0 0 := by
-- proof
  apply StatMech.Walls.bgn_idx_origin L hL

/--
[bgn_ground_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean)
-/
@[path]
private lemma bgn_ground_common_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) = bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) ∧ bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) ≠ bgn_idx L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bgn_ground_common L hL

/--
[bgn_sameTrif_classes_laminar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean)
-/
@[path]
private lemma bgn_sameTrif_classes_laminar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {u a b : Site d} :
-- imply
  bgn_boundaryClass ω L R u a = bgn_boundaryClass ω L R u b ∨ Disjoint (bgn_boundaryClass ω L R u a) (bgn_boundaryClass ω L R u b) := by
-- proof
  apply StatMech.Walls.bgn_sameTrif_classes_laminar ω L R u a b

/--
[bgn_reach_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean)
-/
@[path]
private lemma bgn_reach_isolated_eq
  {d : ℕ}
  {H : SimpleGraph V}
  {u : V}
  {a : V}
-- given
  (hiso : ∀ z, ¬ H.Adj u z)
  (h : H.Reachable a u) :
-- imply
  a = u := by
-- proof
  apply StatMech.Walls.bgn_reach_isolated hiso h

/--
[bgn_crossing_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean)
-/
@[path]
private lemma bgn_crossing_witness_eq
  {d : ℕ} :
-- imply
  (bgn_W.Adj 0 2 ∧ bgn_W.Adj 0 3 ∧ bgn_W.Adj 0 6 ∧ ¬ (bkg_deleteVertex bgn_W 0).Reachable 2 3 ∧ ¬ (bkg_deleteVertex bgn_W 0).Reachable 2 6 ∧ ¬ (bkg_deleteVertex bgn_W 0).Reachable 3 6) ∧ (bgn_W.Adj 1 4 ∧ bgn_W.Adj 1 5 ∧ bgn_W.Adj 1 6 ∧ ¬ (bkg_deleteVertex bgn_W 1).Reachable 4 5 ∧ ¬ (bkg_deleteVertex bgn_W 1).Reachable 4 6 ∧ ¬ (bkg_deleteVertex bgn_W 1).Reachable 5 6) ∧ ((bkg_deleteVertex bgn_W 0).Reachable 1 6 ∧ (bkg_deleteVertex bgn_W 1).Reachable 0 6) ∧ ((bkg_deleteVertex bgn_W 0).Reachable 1 4 ∧ ¬ (bkg_deleteVertex bgn_W 1).Reachable 0 4) ∧ ((bkg_deleteVertex bgn_W 1).Reachable 0 2 ∧ ¬ (bkg_deleteVertex bgn_W 0).Reachable 1 2) := by
-- proof
  apply StatMech.Walls.bgn_crossing_witness

/--
[bgn_forest_iff_bc69](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean)
-/
@[path]
private lemma bgn_forest_iff_bc69_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bgn_forest_iff_bc69 ω L R

/--
[bgn_count_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean)
-/
@[path]
private lemma bgn_count_of_forest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bkg_ClassicalForestData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bgn_count_of_forest ω L R h

/--
[bgn_bk_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean)
-/
@[path]
private lemma bgn_bk_of_forest_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bgn_bk_of_forest p hp1 hp0 hdata

/--
[bgn_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean)
-/
@[path]
private lemma bgn_status_eq
  {d : ℕ} :
-- imply
  (∀ (L : ℕ), 1 ≤ L → bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) = bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) ∧ bgn_idx L (bc57_pt ((L : ℤ) + 1) 1) ≠ bgn_idx L (0 : Site 2)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (u a b : Site d), bgn_boundaryClass ω L R u a = bgn_boundaryClass ω L R u b ∨ Disjoint (bgn_boundaryClass ω L R u a) (bgn_boundaryClass ω L R u b)) ∧ ((bkg_deleteVertex bgn_W 0).Reachable 1 6 ∧ (bkg_deleteVertex bgn_W 1).Reachable 0 6 ∧ (bkg_deleteVertex bgn_W 0).Reachable 1 4 ∧ ¬ (bkg_deleteVertex bgn_W 1).Reachable 0 4 ∧ (bkg_deleteVertex bgn_W 1).Reachable 0 2 ∧ ¬ (bkg_deleteVertex bgn_W 0).Reachable 1 2) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R) ∧ (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
-- proof
  apply StatMech.Walls.bgn_status


-- created on 2026-10-23
