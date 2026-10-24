import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc74disjointforest
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc74_fiber_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_fiber_subset_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)} :
-- imply
  bc73_fiber ω L R c ⊆ bc61_coarseTrifFinset ω L R := by
-- proof
  apply StatMech.Walls.bc74_fiber_subset ω L R c

/--
[bc74_fiber_card_le_coarseTcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_fiber_card_le_coarseTcount_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)} :
-- imply
  (bc73_fiber ω L R c).card ≤ bc61_coarseTcount ω L R := by
-- proof
  apply StatMech.Walls.bc74_fiber_card_le_coarseTcount ω L R c

/--
[bc74_sublatticeForest_of_fullCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_sublatticeForest_of_fullCount_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc74_sublatticeForest_of_fullCount ω L R h

/--
[bc74_sublatticeForest_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_sublatticeForest_of_globalForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc74_sublatticeForest_of_globalForest ω L R h

/--
[bc74_sublatticeForest_of_forestNeighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_sublatticeForest_of_forestNeighbours_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc71_GnForestNeighbours ω L R) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc74_sublatticeForest_of_forestNeighbours ω L R h

/--
[bc74_fiber_mem_gnTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_fiber_mem_gnTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {y : Site d}
-- given
  (hy : y ∈ bc73_fiber ω L R c) :
-- imply
  bc67_IsGnTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc74_fiber_mem_gnTrif ω L R c hy

/--
[bc74_fiber_disjointBoxes_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_fiber_disjointBoxes_deg3_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {y : Site d}
-- given
  (hy : y ∈ bc73_fiber ω L R c) :
-- imply
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : y ∈ S) (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).Adj), 3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).degree ⟨y, hyS⟩ := by
-- proof
  apply StatMech.Walls.bc74_fiber_disjointBoxes_deg3 ω L R c hy

/--
[bc74_fiber_leaf_inject](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_fiber_leaf_inject_eq
  {d : ℕ}
  {p : Site d → Prop}
  {S : Set (Subtype p)} :
-- imply
  Set.InjOn (Subtype.val : Subtype p → Site d) S := by
-- proof
  apply StatMech.Walls.bc74_fiber_leaf_inject S

/--
[bc74_fiber_count_of_fiberForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_fiber_count_of_fiberForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
-- given
  (h : bc74_FiberForest ω L R c) :
-- imply
  (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc74_fiber_count_of_fiberForest ω L R c h

/--
[bc74_sublatticeForest_of_fiberForests](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_sublatticeForest_of_fiberForests_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : ∀ c : Fin d → Fin (2 * L + 1), bc74_FiberForest ω L R c) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc74_sublatticeForest_of_fiberForests ω L R h

/--
[bc74_fiber_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_fiber_mem_box_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {y : Site d}
-- given
  (hy : y ∈ bc73_fiber ω L R c) :
-- imply
  y ∈ box d R := by
-- proof
  apply StatMech.Walls.bc74_fiber_mem_box ω L R c hy

/--
[bc74_fiberForest_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_fiberForest_of_globalForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc74_FiberForest ω L R c := by
-- proof
  apply StatMech.Walls.bc74_fiberForest_of_globalForest ω L R c h

/--
[bc74_fiberForest_of_emptyFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_fiberForest_of_emptyFiber_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {z₀ z₁ : Site d}
-- given
  (hempty : bc73_fiber ω L R c = ∅)
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁) :
-- imply
  bc74_FiberForest ω L R c := by
-- proof
  apply StatMech.Walls.bc74_fiberForest_of_emptyFiber ω L R c hempty hz₀ hz₁ hzne

/--
[bc74_sublatticeForest_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_sublatticeForest_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : bc61_coarseTrifFinset ω L R = ∅) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc74_sublatticeForest_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bc74_bk_count_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_bk_count_closed_eq
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
  apply StatMech.Walls.bc74_bk_count_closed μ hd L hexp hforest hexist

/--
[bc74_bk_count_closed_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_bk_count_closed_of_globalForest_eq
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
  apply StatMech.Walls.bc74_bk_count_closed_of_globalForest μ hd L hexp hGlobal hexist

/--
[bc74_upperLines_sameResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_upperLines_sameResidue_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  bc73_resVec L (0 : Site 2) = bc73_resVec L (bc57_pt (2 * (L : ℤ) + 1) 0) := by
-- proof
  apply StatMech.Walls.bc74_upperLines_sameResidue L

/--
[bc74_upperLines_sublattice_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_upperLines_sublattice_disjoint_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) := by
-- proof
  apply StatMech.Walls.bc74_upperLines_sublattice_disjoint L

/--
[bc74_upperLines_deg3_sublattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_upperLines_deg3_sublattice_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (hyS : (0 : Site 2) ∈ S) (_ : DecidableRel ((bc72_quotGraph (openSubgraph 2 bc60_upperLines) (bc72_collapseBox L (0 : Site 2))).induce S).Adj), 3 ≤ ((bc72_quotGraph (openSubgraph 2 bc60_upperLines) (bc72_collapseBox L (0 : Site 2))).induce S).degree ⟨0, hyS⟩ := by
-- proof
  apply StatMech.Walls.bc74_upperLines_deg3_sublattice hL

/--
[bc74_upperLines_arms_can_share_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_upperLines_arms_can_share_boundary_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bc74_upperLines_arms_can_share_boundary L

/--
[bc74_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc74disjointforest.lean)
-/
@[path]
private lemma bc74_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)), bc74_FiberForest ω L R c → (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)) (y : Site d), y ∈ bc73_fiber ω L R c → ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : y ∈ S) (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).Adj), 3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L y)).induce S).degree ⟨y, hyS⟩) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc71_GnForestNeighbours ω L R → bc73_SublatticeForest ω L R) := by
-- proof
  apply StatMech.Walls.bc74_status


-- created on 2026-10-23
