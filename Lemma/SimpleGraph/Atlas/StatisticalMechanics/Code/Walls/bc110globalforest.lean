import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc110globalforest
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc110_globalForest_of_contracted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc110globalforest.lean)
-/
@[path]
private lemma bc110_globalForest_of_contracted_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc103_ContractedTrifGraph ω L R) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc110_globalForest_of_contracted ω L R h

/--
[bc110_globalForest_all_free_except_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc110globalforest.lean)
-/
@[path]
private lemma bc110_globalForest_all_free_except_contraction_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc103_ContractedTrifGraph ω L R) :
-- imply
  bc69_Gn_globalForest ω L R ∧ (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (osf_spanForest G).IsAcyclic) ∧ (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel (osf_spanForest G).Adj] {u v₁ v₂ v₃ : V}, G.Adj u v₁ → G.Adj u v₂ → G.Adj u v₃ → ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ → ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ → ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ → 3 ≤ (osf_spanForest G).degree u) := by
-- proof
  apply StatMech.Walls.bc110_globalForest_all_free_except_contraction ω L R h

/--
[bc110_contractionArm_of_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc110globalforest.lean)
-/
@[path]
private lemma bc110_contractionArm_of_trif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc67_IsGnTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧ ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧ (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧ (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧ (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc110_contractionArm_of_trif ω L h

/--
[bc110_contractionArm_of_coarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc110globalforest.lean)
-/
@[path]
private lemma bc110_contractionArm_of_coarseTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  bc67_IsGnTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc110_contractionArm_of_coarseTrif ω L h

/--
[bc110_globalForest_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc110globalforest.lean)
-/
@[path]
private lemma bc110_globalForest_of_noTrif_eq
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
  apply StatMech.Walls.bc110_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bc110_contractedGraph_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc110globalforest.lean)
-/
@[path]
private lemma bc110_contractedGraph_of_noTrif_eq
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
  bc103_ContractedTrifGraph ω L R := by
-- proof
  apply StatMech.Walls.bc110_contractedGraph_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bc110_globalForest_of_noTrif_via_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc110globalforest.lean)
-/
@[path]
private lemma bc110_globalForest_of_noTrif_via_contraction_eq
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
  apply StatMech.Walls.bc110_globalForest_of_noTrif_via_contraction ω L R hz₀ hz₁ hzne hno

/--
[bc110_count_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc110globalforest.lean)
-/
@[path]
private lemma bc110_count_of_globalForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc110_count_of_globalForest ω L R h

/--
[bc110_bk_count_half_closes_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc110globalforest.lean)
-/
@[path]
private lemma bc110_bk_count_half_closes_of_globalForest_eq
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
  apply StatMech.Walls.bc110_bk_count_half_closes_of_globalForest μ hd hinv hfe L hGlobal hcoarseRoute

/--
[bc110_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc110globalforest.lean)
-/
@[path]
private lemma bc110_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc103_ContractedTrifGraph ω L R → bc69_Gn_globalForest ω L R) ∧ (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel (osf_spanForest G).Adj] (u v₁ v₂ v₃ : V), G.Adj u v₁ → G.Adj u v₂ → G.Adj u v₃ → ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ → ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ → ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ → 3 ≤ (osf_spanForest G).degree u) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d), bc67_IsGnTrifurcation ω L y → ∃ a₁ a₂ a₃ : Site d, (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc110_status


-- created on 2026-10-23
