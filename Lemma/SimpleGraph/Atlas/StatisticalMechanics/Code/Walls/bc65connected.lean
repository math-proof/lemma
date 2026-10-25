import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc65connected.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc65_connectedCoarseForest_iff_armEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_connectedCoarseForest_iff_armEmbedding_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bc65_ConnectedCoarseForest ω L R ↔ bc63_CoarseArmEmbedding ω L R := by
-- proof
  apply StatMech.Walls.bc65_connectedCoarseForest_iff_armEmbedding ω L R

/--
[bc65_coarseArmEmbedding_of_connectedForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_coarseArmEmbedding_of_connectedForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc65_ConnectedCoarseForest ω L R) :
-- imply
  bc63_CoarseArmEmbedding ω L R := by
-- proof
  apply StatMech.Walls.bc65_coarseArmEmbedding_of_connectedForest ω L R h

/--
[bc65_coarseTcount_le_boundary_of_connectedForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_coarseTcount_le_boundary_of_connectedForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc65_ConnectedCoarseForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc65_coarseTcount_le_boundary_of_connectedForest ω L R h

/--
[bc65_connected_leaf_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_connected_leaf_count_eq
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
  apply StatMech.Walls.bc65_connected_leaf_count G hacyc hmin

/--
[bc65_cat2G_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_cat2G_isTree_eq
  {d : ℕ} :
-- imply
  bc65_cat2G.IsTree := by
-- proof
  apply StatMech.Walls.bc65_cat2G_isTree

/--
[bc65_caterpillar2_leafCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_caterpillar2_leafCount_eq
  {d : ℕ} :
-- imply
  (univ.filter (fun v => 3 ≤ bc65_cat2G.degree v)).card = 2 ∧ (univ.filter (fun v => bc65_cat2G.degree v = 1)).card = 4 := by
-- proof
  apply StatMech.Walls.bc65_caterpillar2_leafCount

/--
[bc65_caterpillar2_savings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_caterpillar2_savings_eq
  {d : ℕ} :
-- imply
  (univ.filter (fun v => bc65_cat2G.degree v = 1)).card < 3 * (univ.filter (fun v => 3 ≤ bc65_cat2G.degree v)).card := by
-- proof
  apply StatMech.Walls.bc65_caterpillar2_savings

/--
[bc65_cat3G_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_cat3G_isTree_eq
  {d : ℕ} :
-- imply
  bc65_cat3G.IsTree := by
-- proof
  apply StatMech.Walls.bc65_cat3G_isTree

/--
[bc65_cat3G_leafCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_cat3G_leafCount_eq
  {d : ℕ} :
-- imply
  (univ.filter (fun v => 3 ≤ bc65_cat3G.degree v)).card = 3 ∧ (univ.filter (fun v => bc65_cat3G.degree v = 1)).card = 5 := by
-- proof
  apply StatMech.Walls.bc65_cat3G_leafCount

/--
[bc65_cat3G_savings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_cat3G_savings_eq
  {d : ℕ} :
-- imply
  (univ.filter (fun v => bc65_cat3G.degree v = 1)).card < 3 * (univ.filter (fun v => 3 ≤ bc65_cat3G.degree v)).card := by
-- proof
  apply StatMech.Walls.bc65_cat3G_savings

/--
[bc65_connectedForest_of_boundaryInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_connectedForest_of_boundaryInjection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hinj : bc64_CoarseBoundaryInjection ω L R) :
-- imply
  bc65_ConnectedCoarseForest ω L R := by
-- proof
  apply StatMech.Walls.bc65_connectedForest_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj

/--
[bc65_connectedForest_of_forestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_connectedForest_of_forestData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {W : Type}
  [Fintype W]
  [Nonempty W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {ιT : Site d → W}
  {lamL : W → Site d}
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hdeg3 : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → 3 ≤ G.degree (ιT y))
  (hιinj : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → ∀ z, z ∈ box d R → bc61_IsCoarseTrifurcation ω L z → ιT y = ιT z → y = z)
  (hlammap : ∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R)
  (hlaminj : Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))) :
-- imply
  bc65_ConnectedCoarseForest ω L R := by
-- proof
  apply StatMech.Walls.bc65_connectedForest_of_forestData ω L R W G ιT lamL hacyc hmin hdeg3 hιinj hlammap hlaminj

/--
[bc65_cat2G_min_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_cat2G_min_degree_eq
  {d : ℕ} :
-- imply
  ∀ v : Fin 6, 1 ≤ bc65_cat2G.degree v := by
-- proof
  apply StatMech.Walls.bc65_cat2G_min_degree

/--
[bc65_cat3G_min_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_cat3G_min_degree_eq
  {d : ℕ} :
-- imply
  ∀ v : Fin 8, 1 ≤ bc65_cat3G.degree v := by
-- proof
  apply StatMech.Walls.bc65_cat3G_min_degree

/--
[bc65_connectedForest_caterpillar2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_connectedForest_caterpillar2_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y₀ y₁ : Site d}
  {lamL : Fin 6 → Site d}
-- given
  (_hy₀box : y₀ ∈ box d R)
  (_hy₁box : y₁ ∈ box d R)
  (_hyne : y₀ ≠ y₁)
  (_hy₀tri : bc61_IsCoarseTrifurcation ω L y₀)
  (_hy₁tri : bc61_IsCoarseTrifurcation ω L y₁)
  (hpair : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → y = y₀ ∨ y = y₁)
  (hlammap : ∀ v, bc65_cat2G.degree v = 1 → lamL v ∈ vertexBoundary d R)
  (hlaminj : Set.InjOn lamL (univ.filter (fun v => bc65_cat2G.degree v = 1))) :
-- imply
  bc65_ConnectedCoarseForest ω L R := by
-- proof
  apply StatMech.Walls.bc65_connectedForest_caterpillar2 ω L R _hy₀box _hy₁box _hyne _hy₀tri _hy₁tri hpair lamL hlammap hlaminj

/--
[bc65_infiniteClusters_top_null_of_connectedForest_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_infiniteClusters_top_null_of_connectedForest_route_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hconn : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc65_ConnectedCoarseForest ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc65_infiniteClusters_top_null_of_connectedForest_route μ hd hinv hfe L hconn hcoarseRoute

/--
[bc65_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean)
-/
@[path]
private lemma bc65_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧ ((univ.filter (fun v => bc65_cat2G.degree v = 1)).card < 3 * (univ.filter (fun v => 3 ≤ bc65_cat2G.degree v)).card) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc65_ConnectedCoarseForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → bc64_CoarseBoundaryInjection ω L R → bc65_ConnectedCoarseForest ω L R) := by
-- proof
  apply StatMech.Walls.bc65_status


-- created on 2026-10-23
