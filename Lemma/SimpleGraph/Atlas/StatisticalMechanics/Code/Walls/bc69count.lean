import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc69count.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc69_subtypeVal_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_subtypeVal_injOn_eq
  {d : ℕ}
  {p : Site d → Prop}
  {S : Set (Subtype p)} :
-- imply
  Set.InjOn (Subtype.val : Subtype p → Site d) S := by
-- proof
  apply StatMech.Walls.bc69_subtypeVal_injOn S

/--
[bc69_box_zero_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_box_zero_mem_eq
  {d : ℕ}
  {d R : ℕ} :
-- imply
  (0 : Site d) ∈ box d R := by
-- proof
  apply StatMech.Walls.bc69_box_zero_mem d R

/--
[bc69_forestData_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_forestData_of_globalForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc68_GnForestData ω L R := by
-- proof
  apply StatMech.Walls.bc69_forestData_of_globalForest ω L R h

/--
[bc69_count_via_leafBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_count_via_leafBound_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc69_count_via_leafBound ω L R h

/--
[bc69_coarseTcount_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_coarseTcount_le_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc69_coarseTcount_le_boundary ω L R h

/--
[bc69_leaf_count_absorbs_shared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_leaf_count_absorbs_shared_eq
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
  apply StatMech.Walls.bc69_leaf_count_absorbs_shared G hacyc hmin

/--
[bc69_leaf_card_le_boundary_subtype](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_leaf_card_le_boundary_subtype_eq
  {d : ℕ}
  {R : ℕ}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  {G : SimpleGraph (↑S : Type)}
  [DecidableRel G.Adj]
-- given
  (hlammap : ∀ v : (↑S : Type), G.degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
-- imply
  (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc69_leaf_card_le_boundary_subtype R G hlammap

/--
[bc69_single_edge_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_single_edge_degree_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {a b : V}
  [DecidableRel (SimpleGraph.fromEdgeSet {s(a,b)}).Adj]
-- given
  (hab : a ≠ b) :
-- imply
  (SimpleGraph.fromEdgeSet {s(a,b)}).degree a = 1 := by
-- proof
  apply StatMech.Walls.bc69_single_edge_degree a b hab

/--
[bc69_single_edge_degree_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_single_edge_degree_b_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {a b : V}
  [DecidableRel (SimpleGraph.fromEdgeSet {s(a,b)}).Adj]
-- given
  (hab : a ≠ b) :
-- imply
  (SimpleGraph.fromEdgeSet {s(a,b)}).degree b = 1 := by
-- proof
  apply StatMech.Walls.bc69_single_edge_degree_b a b hab

/--
[bc69_single_edge_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_single_edge_acyclic_eq
  {d : ℕ}
  [DecidableEq V]
  {a b : V}
-- given
  (hab : a ≠ b) :
-- imply
  (SimpleGraph.fromEdgeSet {s(a,b)}).IsAcyclic := by
-- proof
  apply StatMech.Walls.bc69_single_edge_acyclic a b hab

/--
[bc69_globalForest_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_globalForest_of_noTrif_eq
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
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc69_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bc69_infiniteClusters_top_null_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_infiniteClusters_top_null_of_globalForest_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc69_infiniteClusters_top_null_of_globalForest μ hd hinv hfe L hGlobal hcoarseRoute

/--
[bc69_upperLines_boundary_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_upperLines_boundary_mem_eq
  {d : ℕ}
  {R : ℕ}
  {i : Fin 3}
-- given
  (hR3 : 4 ≤ R) :
-- imply
  bc57_pt (R : ℤ) ((i : ℤ) + 1) ∈ box 2 R := by
-- proof
  apply StatMech.Walls.bc69_upperLines_boundary_mem hR3 i

/--
[bc69_upperLines_globalForest_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_upperLines_globalForest_count_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest bc60_upperLines L R) :
-- imply
  bc61_coarseTcount bc60_upperLines L R ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bc69_upperLines_globalForest_count h

/--
[bc69_upperLines_arms_reach_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_upperLines_arms_reach_distinct_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (hLR : L + 1 ≤ R)
  (hR3 : 4 ≤ R) :
-- imply
  (∀ i : Fin 3, (bc67_contractedLattice bc60_upperLines L (0 : Site 2)).Reachable (bc57_pt ((L : ℤ) + 1) ((i : ℤ) + 1)) (bc57_pt (R : ℤ) ((i : ℤ) + 1)) ∧ bc57_pt (R : ℤ) ((i : ℤ) + 1) ∈ vertexBoundary 2 R) ∧ Function.Injective (fun i : Fin 3 => bc57_pt (R : ℤ) ((i : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bc69_upperLines_arms_reach_distinct hLR hR3

/--
[bc69_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc69count.lean)
-/
@[path]
private lemma bc69_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧ (∀ (R : ℕ) (S : Set (↑(box d R) : Type)), Set.InjOn (Subtype.val : (↑(box d R) : Type) → Site d) S) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc69_status


-- created on 2026-10-23
