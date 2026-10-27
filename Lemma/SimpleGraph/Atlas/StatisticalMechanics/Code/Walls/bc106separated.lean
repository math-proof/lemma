import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc106separated.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc106_origin_onSublattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_origin_onSublattice_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  bc73_onSublattice L (0 : Site d) := by
-- proof
  apply StatMech.Walls.bc106_origin_onSublattice L

/--
[bc106_boxes_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_boxes_disjoint_eq
  {d : ℕ}
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y z : Site d}
-- given
  (hy : bc106_SeparatedCoarseTrif ω L y)
  (hz : bc106_SeparatedCoarseTrif ω L z)
  (hne : y ≠ z) :
-- imply
  Disjoint (bc61_boxAround d L y) (bc61_boxAround d L z) := by
-- proof
  apply StatMech.Walls.bc106_boxes_disjoint hy hz hne

/--
[bc106_far_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_far_of_separated_eq
  {d : ℕ}
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y z : Site d}
-- given
  (hy : bc106_SeparatedCoarseTrif ω L y)
  (hz : bc106_SeparatedCoarseTrif ω L z)
  (hne : y ≠ z) :
-- imply
  ∃ i, 2 * L < ((y - z) i).natAbs := by
-- proof
  apply StatMech.Walls.bc106_far_of_separated hy hz hne

/--
[bc106_isCoarseTrif_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_isCoarseTrif_of_separated_eq
  {d : ℕ}
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (h : bc106_SeparatedCoarseTrif ω L y) :
-- imply
  bc61_IsCoarseTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc106_isCoarseTrif_of_separated h

/--
[bc106_gnTrif_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_gnTrif_of_separated_eq
  {d : ℕ}
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (h : bc106_SeparatedCoarseTrif ω L y) :
-- imply
  bc67_IsGnTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc106_gnTrif_of_separated h

/--
[bc106_](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106__eq
  {d : ℕ}
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y z : Site d}
-- given
  (hy : bc106_SeparatedCoarseTrif ω L y)
  (hz : bc106_SeparatedCoarseTrif ω L z)
  (hyz : y = z) :
-- imply
  y = z := by
-- proof
  apply StatMech.Walls.bc106_ hy hz hyz

/--
[bc106_supervertex_sites_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_supervertex_sites_distinct_eq
  {d : ℕ}
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y z : Site d}
-- given
  (hy : bc106_SeparatedCoarseTrif ω L y)
  (hz : bc106_SeparatedCoarseTrif ω L z)
  (hne : y ≠ z) :
-- imply
  y ∈ bc61_boxAround d L y ∧ y ∉ bc61_boxAround d L z := by
-- proof
  apply StatMech.Walls.bc106_supervertex_sites_distinct hy hz hne

/--
[bc106_resVec_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_resVec_eq_zero_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d}
-- given
  (hy : bc73_onSublattice L y) :
-- imply
  bc73_resVec L y = 0 := by
-- proof
  apply StatMech.Walls.bc106_resVec_eq_zero hy

/--
[bc106_separatedTrifFinset_eq_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_separatedTrifFinset_eq_fiber_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bc106_separatedTrifFinset ω L R = bc73_fiber ω L R 0 := by
-- proof
  apply StatMech.Walls.bc106_separatedTrifFinset_eq_fiber ω L R

/--
[bc106_separatedTcount_eq_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_separatedTcount_eq_fiber_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bc106_separatedTcount ω L R = (bc73_fiber ω L R 0).card := by
-- proof
  apply StatMech.Walls.bc106_separatedTcount_eq_fiber ω L R

/--
[bc106_separatedTrifFinset_pairwise_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_separatedTrifFinset_pairwise_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  (bc106_separatedTrifFinset ω L R : Set (Site d)).Pairwise (fun y y' => Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y')) := by
-- proof
  apply StatMech.Walls.bc106_separatedTrifFinset_pairwise_disjoint ω L R

/--
[bc106_separated_count_le_boundary_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_separated_count_le_boundary_of_forest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc73_SublatticeForest ω L R) :
-- imply
  bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc106_separated_count_le_boundary_of_forest ω L R h

/--
[bc106_separatedContractedTrifGraph_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_separatedContractedTrifGraph_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc106_SeparatedCoarseTrif ω L y) :
-- imply
  bc106_SeparatedContractedTrifGraph ω L R := by
-- proof
  apply StatMech.Walls.bc106_separatedContractedTrifGraph_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bc106_separatedCount_of_contractedGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_separatedCount_of_contractedGraph_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc106_SeparatedContractedTrifGraph ω L R) :
-- imply
  bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc106_separatedCount_of_contractedGraph ω L R h

/--
[bc106_separatedContractedTrifGraph_of_bc103](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_separatedContractedTrifGraph_of_bc103_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc103_ContractedTrifGraph ω L R) :
-- imply
  bc106_SeparatedContractedTrifGraph ω L R := by
-- proof
  apply StatMech.Walls.bc106_separatedContractedTrifGraph_of_bc103 ω L R h

/--
[bc106_origin_event_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_origin_event_eq_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ} :
-- imply
  bc106_SeparatedCoarseTrif ω L (0 : Site d) ↔ bc61_IsCoarseTrifurcation ω L (0 : Site d) := by
-- proof
  apply StatMech.Walls.bc106_origin_event_eq ω L

/--
[bc106_full_covering_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_full_covering_of_forest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc73_SublatticeForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc106_full_covering_of_forest ω L R h

/--
[bc106_separated_drives_prob_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_separated_drives_prob_zero_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R) :
-- imply
  μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 := by
-- proof
  apply StatMech.Walls.bc106_separated_drives_prob_zero μ hd L hexp hforest

/--
[bc106_separated_drives_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_separated_drives_dichotomy_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc106_separated_drives_dichotomy μ hd L hexp hforest hexist

/--
[bc106_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean)
-/
@[path]
private lemma bc106_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y z : Site d), bc106_SeparatedCoarseTrif ω L y → bc106_SeparatedCoarseTrif ω L z → y ≠ z → Disjoint (bc61_boxAround d L y) (bc61_boxAround d L z)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc103_ContractedTrifGraph ω L R → bc106_SeparatedContractedTrifGraph ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc106_SeparatedContractedTrifGraph ω L R → bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc73_SublatticeForest ω L R → bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ), bc106_SeparatedCoarseTrif ω L (0 : Site d) ↔ bc61_IsCoarseTrifurcation ω L (0 : Site d)) := by
-- proof
  apply StatMech.Walls.bc106_status


-- created on 2026-10-23
