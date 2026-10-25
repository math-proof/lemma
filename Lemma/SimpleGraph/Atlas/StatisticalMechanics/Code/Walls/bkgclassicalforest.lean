import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bkgclassicalforest.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bkg_deleteVertex_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_deleteVertex_adj_eq
  {d : ℕ}
  {Amb : SimpleGraph V}
  {t a b : V} :
-- imply
  (bkg_deleteVertex Amb t).Adj a b ↔ Amb.Adj a b ∧ a ≠ t ∧ b ≠ t := by
-- proof
  apply StatMech.Walls.bkg_deleteVertex_adj Amb t a b

/--
[bkg_deleteVertex_adj_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_deleteVertex_adj_of_le_eq
  {d : ℕ}
  {Amb G : SimpleGraph V}
  {t a b : V}
-- given
  (hle : G ≤ Amb)
  (hab : G.Adj a b)
  (ha : a ≠ t)
  (hb : b ≠ t) :
-- imply
  (bkg_deleteVertex Amb t).Adj a b := by
-- proof
  apply StatMech.Walls.bkg_deleteVertex_adj_of_le hle hab ha hb

/--
[bkg_walkReach_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_walkReach_free_eq
  {d : ℕ}
  {Amb G : SimpleGraph V}
  {t : V}
-- given
  (hle : G ≤ Amb) :
-- imply
  ∀ a b (w : G.Walk a b), t ∉ w.support → (bkg_deleteVertex Amb t).Reachable a b := by
-- proof
  apply StatMech.Walls.bkg_walkReach_free hle t

/--
[bkg_acyclic_of_singleVertexCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_acyclic_of_singleVertexCut_eq
  {d : ℕ}
  {Amb G : SimpleGraph V}
-- given
  (hle : G ≤ Amb)
  (H1 : ∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → ¬ (bkg_deleteVertex Amb t).Reachable a b) :
-- imply
  G.IsAcyclic := by
-- proof
  apply StatMech.Walls.bkg_acyclic_of_singleVertexCut Amb G hle H1

/--
[bkg_reachable_eq_of_edgeless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_reachable_eq_of_edgeless_eq
  {d : ℕ}
  {H : SimpleGraph V}
  {a b : V}
-- given
  (he : ∀ u v, ¬ H.Adj u v)
  (h : H.Reachable a b) :
-- imply
  a = b := by
-- proof
  apply StatMech.Walls.bkg_reachable_eq_of_edgeless he h

/--
[bkg_step_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_step_witness_eq
  {d : ℕ} :
-- imply
  bc70_star4.IsAcyclic := by
-- proof
  apply StatMech.Walls.bkg_step_witness

/--
[bkg_trif_three_arms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_trif_three_arms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d}
  {arm : Fin 3 → Site d}
-- given
  (hR : 1 ≤ R)
  (harmbox : ∀ i, arm i ∈ box d R)
  (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L y) ω) (arm i)).Infinite)
  (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L y).Reachable (arm i) (arm j)) :
-- imply
  ∃ tip : Fin 3 → Site d, (∀ i, (bc67_contractedLattice ω L y).Reachable (arm i) (tip i)) ∧ (∀ i, tip i ∈ vertexBoundary d R) ∧ (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L y).Reachable (tip i) (tip j)) := by
-- proof
  apply StatMech.Walls.bkg_trif_three_arms ω L R hR y arm harmbox harminf harmsep

/--
[bkg_globalForest_of_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_globalForest_of_classical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bkg_ClassicalForestData ω L R) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bkg_globalForest_of_classical ω L R h

/--
[bkg_coarseTcount_of_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_coarseTcount_of_classical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bkg_ClassicalForestData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bkg_coarseTcount_of_classical ω L R h

/--
[bkg_bc69_of_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_bc69_of_classical_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (hdata : ∀ ω : ConfigSpace (Sym2 (Site d)), bkg_ClassicalForestData ω L R) :
-- imply
  ∀ ω : ConfigSpace (Sym2 (Site d)), bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bkg_bc69_of_classical L R hdata

/--
[bkg_bk_uniqueness_of_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_bk_uniqueness_of_classical_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bkg_bk_uniqueness_of_classical p hp1 hp0 hdata

/--
[bkg_top_null_of_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_top_null_of_classical_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bkg_top_null_of_classical p hp1 hp0 hdata

/--
[bkg_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean)
-/
@[path]
private lemma bkg_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} (Amb G : SimpleGraph V), G ≤ Amb → (∀ t a b, G.Adj t a → G.Adj t b → a ≠ b → ¬ (bkg_deleteVertex Amb t).Reachable a b) → G.IsAcyclic) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bkg_ClassicalForestData ω L R → bc69_Gn_globalForest ω L R) ∧ (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
-- proof
  apply StatMech.Walls.bkg_status


-- created on 2026-10-23
