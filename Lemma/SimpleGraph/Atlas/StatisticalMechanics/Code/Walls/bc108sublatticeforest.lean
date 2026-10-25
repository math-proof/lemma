import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc108sublatticeforest
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc108_fiber_subset_coarseTrifFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_fiber_subset_coarseTrifFinset_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)} :
-- imply
  bc73_fiber ω L R c ⊆ bc61_coarseTrifFinset ω L R := by
-- proof
  apply StatMech.Walls.bc108_fiber_subset_coarseTrifFinset ω L R c

/--
[bc108_fiber_card_le_coarseTcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_fiber_card_le_coarseTcount_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)} :
-- imply
  (bc73_fiber ω L R c).card ≤ bc61_coarseTcount ω L R := by
-- proof
  apply StatMech.Walls.bc108_fiber_card_le_coarseTcount ω L R c

/--
[bc108_sublatticeForest_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_sublatticeForest_of_globalForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc108_sublatticeForest_of_globalForest ω L R h

/--
[bc108_sublatticeForest_of_contractedGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_sublatticeForest_of_contractedGraph_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc103_ContractedTrifGraph ω L R) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc108_sublatticeForest_of_contractedGraph ω L R h

/--
[bc108_separatedCount_le_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_separatedCount_le_of_globalForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc108_separatedCount_le_of_globalForest ω L R h

/--
[bc108_full_covering_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_full_covering_of_globalForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc108_full_covering_of_globalForest ω L R h

/--
[bc108_hub_three_distinct_forestNeighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_hub_three_distinct_forestNeighbours_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel (osf_spanForest G).Adj]
  {u v₁ v₂ v₃ : V}
-- given
  (hadj₁ : G.Adj u v₁)
  (hadj₂ : G.Adj u v₂)
  (hadj₃ : G.Adj u v₃)
  (hcut₁₂ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂)
  (hcut₁₃ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃)
  (hcut₂₃ : ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃) :
-- imply
  3 ≤ (osf_spanForest G).degree u := by
-- proof
  apply StatMech.Walls.bc108_hub_three_distinct_forestNeighbours G hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃

/--
[bc108_hub_arms_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_hub_arms_distinct_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {u v₁ v₂ v₃ : V}
-- given
  (hcut₁₂ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂)
  (hcut₁₃ : ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃)
  (hcut₂₃ : ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃) :
-- imply
  v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ := by
-- proof
  apply StatMech.Walls.bc108_hub_arms_distinct hcut₁₂ hcut₁₃ hcut₂₃

/--
[bc108_crosshub_leaves_can_share](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_crosshub_leaves_can_share_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bc108_crosshub_leaves_can_share L

/--
[bc108_boundary_injection_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_boundary_injection_refuted_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  (Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0))) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bc108_boundary_injection_refuted L

/--
[bc108_bk_count_reduces_to_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_bk_count_reduces_to_globalForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  (bc69_Gn_globalForest ω L R → bc73_SublatticeForest ω L R) ∧ (bc69_Gn_globalForest ω L R → bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc108_bk_count_reduces_to_globalForest ω L R

/--
[bc108_infiniteClusters_top_null_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_infiniteClusters_top_null_of_globalForest_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc108_infiniteClusters_top_null_of_globalForest μ hd L hexp hGlobal hexist

/--
[bc108_sublatticeForest_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_sublatticeForest_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc108_sublatticeForest_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bc108_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc108sublatticeforest.lean)
-/
@[path]
private lemma bc108_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc69_Gn_globalForest ω L R → bc73_SublatticeForest ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)), (bc73_fiber ω L R c).card ≤ bc61_coarseTcount ω L R) ∧ (∀ (L : ℕ), Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) ∧ (∀ {V : Type} {G : SimpleGraph V} (u v₁ v₂ v₃ : V), ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ → ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ → ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ → v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc69_Gn_globalForest ω L R → bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc108_status


-- created on 2026-10-23
