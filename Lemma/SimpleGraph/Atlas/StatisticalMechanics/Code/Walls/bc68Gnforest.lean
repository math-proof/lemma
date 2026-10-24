import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc68Gnforest
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc68_Gn_spanForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_Gn_spanForest_eq
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
  apply StatMech.Walls.bc68_Gn_spanForest ω L R W G ιU lamL hacyc hmin hdeg3 hιinj hlammap hlaminj

/--
[bc68_Gn_subgraph_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_Gn_subgraph_acyclic_eq
  {d : ℕ}
  {G G' : SimpleGraph W}
-- given
  (hsub : G ≤ G')
  (h : G'.IsAcyclic) :
-- imply
  G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bc68_Gn_subgraph_acyclic hsub h

/--
[bc68_Gn_arm_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_Gn_arm_reaches_boundary_eq
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
  apply StatMech.Walls.bc68_Gn_arm_reaches_boundary ω L R hR y a habox hinf

/--
[bc68_Gn_leaf_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_Gn_leaf_count_eq
  {d : ℕ}
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bc68_Gn_leaf_count G hacyc hmin

/--
[bc68_no_shared_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_no_shared_target_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a b z : Site d}
-- given
  (hcut : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a b)
  (haz : (bc67_contractedLattice ω L y).Reachable a z)
  (hbz : (bc67_contractedLattice ω L y).Reachable b z) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.bc68_no_shared_target ω L y a b z hcut haz hbz

/--
[bc68_Gn_singleTrif_distinct_leaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_Gn_singleTrif_distinct_leaves_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
  {a : Fin 3 → Site d}
  {z : Fin 3 → Site d}
-- given
  (hcut01 : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 0) (a 1))
  (hcut02 : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 0) (a 2))
  (hcut12 : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 1) (a 2))
  (hreach : ∀ i, (bc67_contractedLattice ω L y).Reachable (a i) (z i)) :
-- imply
  Function.Injective z := by
-- proof
  apply StatMech.Walls.bc68_Gn_singleTrif_distinct_leaves ω L y a hcut01 hcut02 hcut12 z hreach

/--
[bc68_upperLines_boundaryPt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_upperLines_boundaryPt_eq
  {d : ℕ}
  {R : ℕ}
  {h : ℤ}
-- given
  (hR : 1 ≤ R)
  (hh : 1 ≤ h)
  (hhR : h ≤ (R : ℤ) - 1) :
-- imply
  bc57_pt (R : ℤ) h ∈ vertexBoundary 2 R := by
-- proof
  apply StatMech.Walls.bc68_upperLines_boundaryPt hR hh hhR

/--
[bc68_upperLines_arm_reaches_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_upperLines_arm_reaches_R_eq
  {d : ℕ}
  {L R : ℕ}
  {h : ℤ}
-- given
  (hLR : L + 1 ≤ R)
  (hh : 1 ≤ h) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) (bc57_pt ((L : ℤ) + 1) h) (bc57_pt (R : ℤ) h) := by
-- proof
  apply StatMech.Walls.bc68_upperLines_arm_reaches_R hLR hh

/--
[bc68_upperLines_arms_reach_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_upperLines_arms_reach_distinct_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (hLR : L + 1 ≤ R)
  (hR3 : 4 ≤ R) :
-- imply
  (∀ i : Fin 3, (bc67_contractedLattice bc60_upperLines L (0 : Site 2)).Reachable (bc57_pt ((L : ℤ) + 1) ((i : ℤ) + 1)) (bc57_pt (R : ℤ) ((i : ℤ) + 1)) ∧ bc57_pt (R : ℤ) ((i : ℤ) + 1) ∈ vertexBoundary 2 R) ∧ Function.Injective (fun i : Fin 3 => bc57_pt (R : ℤ) ((i : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bc68_upperLines_arms_reach_distinct hLR hR3

/--
[bc68_connectedForest_of_GnForestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_connectedForest_of_GnForestData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc68_GnForestData ω L R) :
-- imply
  bc65_ConnectedCoarseForest ω L R := by
-- proof
  apply StatMech.Walls.bc68_connectedForest_of_GnForestData ω L R h

/--
[bc68_coarseTcount_le_boundary_of_GnForestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_coarseTcount_le_boundary_of_GnForestData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc68_GnForestData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc68_coarseTcount_le_boundary_of_GnForestData ω L R h

/--
[bc68_infiniteClusters_top_null_of_GnForestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_infiniteClusters_top_null_of_GnForestData_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hGnData : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc68_GnForestData ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc68_infiniteClusters_top_null_of_GnForestData μ hd hinv hfe L hGnData hcoarseRoute

/--
[bc68_multiTrif_shared_boundary_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_multiTrif_shared_boundary_survives_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bc68_multiTrif_shared_boundary_survives L

/--
[bc68_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc68Gnforest.lean)
-/
@[path]
private lemma bc68_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) (a : Fin 3 → Site d) (z : Fin 3 → Site d), ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 0) (a 1) → ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 0) (a 2) → ¬ Connected d (removeSites (bc61_boxAround d L y) ω) (a 1) (a 2) → (∀ i, (bc67_contractedLattice ω L y).Reachable (a i) (z i)) → Function.Injective z) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc68_GnForestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (∀ (L : ℕ), Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) := by
-- proof
  apply StatMech.Walls.bc68_status


-- created on 2026-10-23
