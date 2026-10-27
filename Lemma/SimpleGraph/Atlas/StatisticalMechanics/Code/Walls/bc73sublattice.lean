import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc73sublattice.Part5
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc73_far_of_onSublattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_far_of_onSublattice_eq
  {d : ℕ}
  {L : ℕ}
  {y y' : Site d}
-- given
  (hy : bc73_onSublattice L y)
  (hy' : bc73_onSublattice L y')
  (hne : y ≠ y') :
-- imply
  ∃ i, 2 * L < ((y - y') i).natAbs := by
-- proof
  apply StatMech.Walls.bc73_far_of_onSublattice hy hy' hne

/--
[bc73_sublattice_boxes_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_sublattice_boxes_disjoint_eq
  {d : ℕ}
  {L : ℕ}
  {y y' : Site d}
-- given
  (hy : bc73_onSublattice L y)
  (hy' : bc73_onSublattice L y')
  (hne : y ≠ y') :
-- imply
  Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') := by
-- proof
  apply StatMech.Walls.bc73_sublattice_boxes_disjoint hy hy' hne

/--
[bc73_mem_sublattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_mem_sublattice_eq
  {d : ℕ}
  {L R : ℕ}
  {y : Site d} :
-- imply
  y ∈ bc73_sublattice d L R ↔ y ∈ box d R ∧ bc73_onSublattice L y := by
-- proof
  apply StatMech.Walls.bc73_mem_sublattice

/--
[bc73_sublattice_pairwise_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_sublattice_pairwise_disjoint_eq
  {d : ℕ}
  {L R : ℕ} :
-- imply
  (bc73_sublattice d L R : Set (Site d)).Pairwise (fun y y' => Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y')) := by
-- proof
  apply StatMech.Walls.bc73_sublattice_pairwise_disjoint L R

/--
[bc73_far_of_sameResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_far_of_sameResidue_eq
  {d : ℕ}
  {L : ℕ}
  {y y' : Site d}
-- given
  (hres : bc73_resVec L y = bc73_resVec L y')
  (hne : y ≠ y') :
-- imply
  ∃ i, 2 * L < ((y - y') i).natAbs := by
-- proof
  apply StatMech.Walls.bc73_far_of_sameResidue hres hne

/--
[bc73_sameResidue_boxes_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_sameResidue_boxes_disjoint_eq
  {d : ℕ}
  {L : ℕ}
  {y y' : Site d}
-- given
  (hres : bc73_resVec L y = bc73_resVec L y')
  (hne : y ≠ y') :
-- imply
  Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') := by
-- proof
  apply StatMech.Walls.bc73_sameResidue_boxes_disjoint hres hne

/--
[bc73_fiber_pairwise_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_fiber_pairwise_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)} :
-- imply
  (bc73_fiber ω L R c : Set (Site d)).Pairwise (fun y y' => Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y')) := by
-- proof
  apply StatMech.Walls.bc73_fiber_pairwise_disjoint ω L R c

/--
[bc73_covering](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_covering_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc73_SublatticeForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc73_covering ω L R h

/--
[bc73_const_boundary_vol_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_const_boundary_vol_tendsto_eq
  {d : ℕ}
  {d : ℕ}
  {L : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun R => (((2 * L + 1) ^ d * boxSV_boundaryCard d R : ℕ) : ℝ) / ((boxFinsetBK d R).card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Walls.bc73_const_boundary_vol_tendsto d hd L

/--
[bc73_coarseTrif_prob_eq_zero_of_sublatticeForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_coarseTrif_prob_eq_zero_of_sublatticeForest_eq
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
  apply StatMech.Walls.bc73_coarseTrif_prob_eq_zero_of_sublatticeForest μ hd L hexp hforest

/--
[bc73_infiniteClusters_top_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_infiniteClusters_top_null_eq
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
  apply StatMech.Walls.bc73_infiniteClusters_top_null μ hd L hexp hforest hexist

/--
[bc73_disjointBoxes_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_disjointBoxes_deg3_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bc67_IsGnTrifurcation ω L y) :
-- imply
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : y ∈ S) (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).Adj), 3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).degree ⟨y, hyS⟩ := by
-- proof
  apply StatMech.Walls.bc73_disjointBoxes_deg3 h

/--
[bc73_fiber_empty_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_fiber_empty_bound_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
-- given
  (hempty : bc73_fiber ω L R c = ∅) :
-- imply
  (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc73_fiber_empty_bound ω L R c hempty

/--
[bc73_sublatticeForest_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_sublatticeForest_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hno : bc61_coarseTrifFinset ω L R = ∅) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc73_sublatticeForest_of_noTrif ω L R hno

/--
[bc73_upperLines_sublattice_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_upperLines_sublattice_disjoint_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) := by
-- proof
  apply StatMech.Walls.bc73_upperLines_sublattice_disjoint L

/--
[bc73_upperLines_deg3_sublattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_upperLines_deg3_sublattice_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (hyS : (0 : Site 2) ∈ S) (_ : DecidableRel ((bc72_quotGraph (openSubgraph 2 bc60_upperLines) (bc72_collapseBox L (0 : Site 2))).induce S).Adj), 3 ≤ ((bc72_quotGraph (openSubgraph 2 bc60_upperLines) (bc72_collapseBox L (0 : Site 2))).induce S).degree ⟨0, hyS⟩ := by
-- proof
  apply StatMech.Walls.bc73_upperLines_deg3_sublattice hL

/--
[bc73_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc73sublattice.lean)
-/
@[path]
private lemma bc73_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)), (bc73_fiber ω L R c : Set (Site d)).Pairwise (fun y y' => Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y'))) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc73_SublatticeForest ω L R → bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R) ∧ (1 ≤ d → ∀ L : ℕ, Tendsto (fun R => (((2 * L + 1) ^ d * boxSV_boundaryCard d R : ℕ) : ℝ) / ((boxFinsetBK d R).card : ℝ)) atTop (𝓝 0)) := by
-- proof
  apply StatMech.Walls.bc73_status


-- created on 2026-10-23
