import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc61coarsebox.Part5
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc61_mem_boxAround](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_mem_boxAround_eq
  {d : ℕ}
  {d L : ℕ}
  {y x : Site d} :
-- imply
  x ∈ bc61_boxAround d L y ↔ (x - y) ∈ box d L := by
-- proof
  apply StatMech.Walls.bc61_mem_boxAround

/--
[bc61_boxAround_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_boxAround_zero_eq
  {d : ℕ}
  {d L : ℕ} :
-- imply
  bc61_boxAround d L 0 = boxFinsetBK d L := by
-- proof
  apply StatMech.Walls.bc61_boxAround_zero d L

/--
[bc61_removeBox_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_removeBox_le_eq
  {d : ℕ}
  {d L : ℕ}
  {y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  removeSites (bc61_boxAround d L y) ω ≤ ω := by
-- proof
  apply StatMech.Walls.bc61_removeBox_le d L y ω

/--
[bc61_connected_of_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_connected_of_cut_eq
  {d : ℕ}
  {d L : ℕ}
  {y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (h : Connected d (removeSites (bc61_boxAround d L y) ω) a b) :
-- imply
  Connected d ω a b := by
-- proof
  apply StatMech.Walls.bc61_connected_of_cut h

/--
[bc61_removeBox_apply_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_removeBox_apply_of_notMem_eq
  {d : ℕ}
  {d L : ℕ}
  {y : Site d}
  {a b : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (ha : a ∉ bc61_boxAround d L y)
  (hb : b ∉ bc61_boxAround d L y) :
-- imply
  removeSites (bc61_boxAround d L y) ω s(a, b) = ω s(a, b) := by
-- proof
  apply StatMech.Walls.bc61_removeBox_apply_of_notMem ha hb ω

/--
[bc61_cut_adj_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_cut_adj_connected_eq
  {d : ℕ}
  {d L : ℕ}
  {y : Site d}
  {a b : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hadj : (hypercubicLattice d).Adj a b)
  (hopen : ω s(a, b) = true)
  (ha : a ∉ bc61_boxAround d L y)
  (hb : b ∉ bc61_boxAround d L y) :
-- imply
  Connected d (removeSites (bc61_boxAround d L y) ω) a b := by
-- proof
  apply StatMech.Walls.bc61_cut_adj_connected hadj hopen ha hb

/--
[bc61_mem_boxAround_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_mem_boxAround_zero_eq
  {d : ℕ}
  {L : ℕ}
  {x : Site 2} :
-- imply
  x ∈ bc61_boxAround 2 L 0 ↔ x ∈ box 2 L := by
-- proof
  apply StatMech.Walls.bc61_mem_boxAround_zero

/--
[bc61_pt_outside_boxAround](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_pt_outside_boxAround_eq
  {d : ℕ}
  {L : ℕ}
  {k h : ℤ}
-- given
  (hk : (L : ℤ) < k) :
-- imply
  bc57_pt k h ∉ bc61_boxAround 2 L 0 := by
-- proof
  apply StatMech.Walls.bc61_pt_outside_boxAround hk

/--
[bc61_upperLines_rightArm_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_upperLines_rightArm_reach_eq
  {d : ℕ}
  {L : ℕ}
  {h : ℤ}
  {j : ℕ}
-- given
  (hh : 1 ≤ h) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) (bc57_pt ((L : ℤ) + 1) h) (bc57_pt ((L : ℤ) + 1 + (j : ℤ)) h) := by
-- proof
  apply StatMech.Walls.bc61_upperLines_rightArm_reach hh j

/--
[bc61_upperLines_rightArm_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_upperLines_rightArm_infinite_eq
  {d : ℕ}
  {L : ℕ}
  {h : ℤ}
-- given
  (hh : 1 ≤ h) :
-- imply
  (cluster 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) (bc57_pt ((L : ℤ) + 1) h)).Infinite := by
-- proof
  apply StatMech.Walls.bc61_upperLines_rightArm_infinite hh

/--
[bc61_upperLines_arm_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_upperLines_arm_disconnected_eq
  {d : ℕ}
  {L : ℕ}
  {h h' : ℤ}
-- given
  (hne : h ≠ h') :
-- imply
  ¬ Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) (bc57_pt ((L : ℤ) + 1) h) (bc57_pt ((L : ℤ) + 1) h') := by
-- proof
  apply StatMech.Walls.bc61_upperLines_arm_disconnected hne

/--
[bc61_upperLines_arm_boxAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_upperLines_arm_boxAdjacent_eq
  {d : ℕ}
  {L : ℕ}
  {h : ℤ}
-- given
  (hh : 1 ≤ h)
  (hhL : h ≤ (L : ℤ)) :
-- imply
  ∃ b ∈ bc61_boxAround 2 L 0, (openSubgraph 2 bc60_upperLines).Adj b (bc57_pt ((L : ℤ) + 1) h) := by
-- proof
  apply StatMech.Walls.bc61_upperLines_arm_boxAdjacent hh hhL

/--
[bc61_wholeBox_severs_upperLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_wholeBox_severs_upperLines_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc61_wholeBox_severs_upperLines hL

/--
[bc61_singleSite_fails_upperLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_singleSite_fails_upperLines_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site 2))}
  {a a' : Site 2}
-- given
  (ha : a 1 ≤ 1)
  (ha' : a' 1 ≤ 1)
  (hinf : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite)
  (hinf' : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a').Infinite) :
-- imply
  Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a a' := by
-- proof
  apply StatMech.Walls.bc61_singleSite_fails_upperLines ha ha' hinf hinf'

/--
[bc61_contrast_upperLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_contrast_upperLines_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧ (∀ (G : Finset (Sym2 (Site 2))) (a a' : Site 2), a 1 ≤ 1 → a' 1 ≤ 1 → (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite → (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a').Infinite → Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a a') := by
-- proof
  apply StatMech.Walls.bc61_contrast_upperLines hL

/--
[bc61_mem_coarseTrifFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_mem_coarseTrifFinset_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d} :
-- imply
  y ∈ bc61_coarseTrifFinset ω L R ↔ y ∈ box d R ∧ bc61_IsCoarseTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc61_mem_coarseTrifFinset

/--
[bc61_coarseTcount_le_boundary_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_coarseTcount_le_boundary_of_forest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc61_CoarseForestLeafCount ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc61_coarseTcount_le_boundary_of_forest ω L R h

/--
[bc61_coarseTrif_prob_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_coarseTrif_prob_eq_zero_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {bdry : ℕ → ℕ}
-- given
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R)
  (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
  (hdens : Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0)) :
-- imply
  μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 := by
-- proof
  apply StatMech.Walls.bc61_coarseTrif_prob_eq_zero μ L bdry hexp hbound hvol hdens

/--
[bc61_infiniteClusters_top_null_of_coarse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_infiniteClusters_top_null_of_coarse_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {bdry : ℕ → ℕ}
-- given
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R)
  (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
  (hdens : Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc61_infiniteClusters_top_null_of_coarse μ L bdry hexp hbound hvol hdens hexist

/--
[bc61_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean)
-/
@[path]
private lemma bc61_status_eq
  {d : ℕ} :
-- imply
  (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) ∧ (∀ {L : ℕ}, 3 ≤ L → (∀ (G : Finset (Sym2 (Site 2))) (a a' : Site 2), a 1 ≤ 1 → a' 1 ≤ 1 → (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite → (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a').Infinite → Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a a')) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc61_CoarseForestLeafCount ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) := by
-- proof
  apply StatMech.Walls.bc61_status


-- created on 2026-10-23
