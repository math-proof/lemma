import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc67supervertex.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc67_contractedLattice_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_contractedLattice_adj_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b : Site d} :
-- imply
  (bc67_contractedLattice ω L y).Adj a b ↔ (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Adj a b := by
-- proof
  apply StatMech.Walls.bc67_contractedLattice_adj ω L y a b

/--
[bc67_Gn_deletion_eq_removeSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_Gn_deletion_eq_removeSites_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b : Site d} :
-- imply
  (bc67_contractedLattice ω L y).Reachable a b ↔ Connected d (removeSites (bc61_boxAround d L y) ω) a b := by
-- proof
  apply StatMech.Walls.bc67_Gn_deletion_eq_removeSites ω L y a b

/--
[bc67_contractedLattice_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_contractedLattice_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d} :
-- imply
  bc67_contractedLattice ω L y ≤ openSubgraph d ω := by
-- proof
  apply StatMech.Walls.bc67_contractedLattice_le ω L y

/--
[bc67_connected_of_Gn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_connected_of_Gn_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b : Site d}
-- given
  (h : (bc67_contractedLattice ω L y).Reachable a b) :
-- imply
  Connected d ω a b := by
-- proof
  apply StatMech.Walls.bc67_connected_of_Gn h

/--
[bc67_gnTrif_of_coarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_gnTrif_of_coarseTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  bc67_IsGnTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc67_gnTrif_of_coarseTrif ω L y h

/--
[bc67_coarseTrif_of_gnTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_coarseTrif_of_gnTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc67_IsGnTrifurcation ω L y) :
-- imply
  bc61_IsCoarseTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc67_coarseTrif_of_gnTrif ω L y h

/--
[bc67_coarseTrif_is_G_n_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_coarseTrif_is_G_n_trifurcation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d} :
-- imply
  bc61_IsCoarseTrifurcation ω L y ↔ bc67_IsGnTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc67_coarseTrif_is_G_n_trifurcation ω L y

/--
[bc67_upperLines_is_G_n_trifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_upperLines_is_G_n_trifurcation_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc67_upperLines_is_G_n_trifurcation hL

/--
[bc67_upperLines_Gn_severs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_upperLines_Gn_severs_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (_hL : 3 ≤ L) :
-- imply
  ¬ (bc67_contractedLattice bc60_upperLines L 0).Reachable (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) := by
-- proof
  apply StatMech.Walls.bc67_upperLines_Gn_severs _hL

/--
[bc67_Gn_arm_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_Gn_arm_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y a : Site d}
-- given
  (hR : 1 ≤ R)
  (habox : a ∈ box d R)
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z := by
-- proof
  apply StatMech.Walls.bc67_Gn_arm_reaches_boundary ω L R hR y a habox hinf

/--
[bc67_Gn_singleVertex_trifurcation_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_Gn_singleVertex_trifurcation_degree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc67_IsGnTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧ (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc67_Gn_singleVertex_trifurcation_degree ω L y h

/--
[bc67_Gn_armForest_of_forestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_Gn_armForest_of_forestData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {W : Type}
  [Fintype W]
  [Nonempty W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {ιU : Site d → W}
  {lamL : W → Site d}
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y))
  (hιinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
  (hlammap : ∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R)
  (hlaminj : Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))) :
-- imply
  bc65_ConnectedCoarseForest ω L R := by
-- proof
  apply StatMech.Walls.bc67_Gn_armForest_of_forestData ω L R W G ιU lamL hacyc hmin hdeg3 hιinj hlammap hlaminj

/--
[bc67_Gn_armForest_coarseTcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_Gn_armForest_coarseTcount_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {W : Type}
  [Fintype W]
  [Nonempty W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {ιU : Site d → W}
  {lamL : W → Site d}
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y))
  (hιinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R → bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
  (hlammap : ∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R)
  (hlaminj : Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc67_Gn_armForest_coarseTcount ω L R W G ιU lamL hacyc hmin hdeg3 hιinj hlammap hlaminj

/--
[bc67_infiniteClusters_top_null_of_GnForest_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_infiniteClusters_top_null_of_GnForest_route_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hGnforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc65_ConnectedCoarseForest ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc67_infiniteClusters_top_null_of_GnForest_route μ hd hinv hfe L hGnforest hcoarseRoute

/--
[bc67_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean)
-/
@[path]
private lemma bc67_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d), (bc67_contractedLattice ω L y).Reachable a b ↔ Connected d (removeSites (bc61_boxAround d L y) ω) a b) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d), bc61_IsCoarseTrifurcation ω L y ↔ bc67_IsGnTrifurcation ω L y) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R → (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite → ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z) ∧ (∀ {L : ℕ}, 3 ≤ L → bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2)) := by
-- proof
  apply StatMech.Walls.bc67_status


-- created on 2026-10-23
