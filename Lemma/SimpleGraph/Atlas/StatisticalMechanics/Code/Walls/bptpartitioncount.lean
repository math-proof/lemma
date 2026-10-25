import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bptpartitioncount.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bpt_mem_boundaryClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean)
-/
@[path]
private lemma bpt_mem_boundaryClass_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x a c : Site d} :
-- imply
  c ∈ bpt_boundaryClass ω L R x a ↔ c ∈ vertexBoundary d R ∧ (bc67_contractedLattice ω L x).Reachable a c := by
-- proof
  apply StatMech.Walls.bpt_mem_boundaryClass

/--
[bpt_trif_three_boundary_classes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean)
-/
@[path]
private lemma bpt_trif_three_boundary_classes_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x : Site d}
  {arm : Fin 3 → Site d}
-- given
  (hR : 1 ≤ R)
  (harmbox : ∀ i, arm i ∈ box d R)
  (harmne : ∀ i, arm i ≠ x)
  (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
  (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) :
-- imply
  ∃ t : Fin 3 → Site d, (∀ i, t i ∈ vertexBoundary d R) ∧ (∀ i, t i ≠ x) ∧ Function.Injective (fun i => (bc67_contractedLattice ω L x).connectedComponentMk (t i)) := by
-- proof
  apply StatMech.Walls.bpt_trif_three_boundary_classes ω L R hR arm harmbox harmne harminf harmsep

/--
[bpt_trif_three_classes_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean)
-/
@[path]
private lemma bpt_trif_three_classes_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x : Site d}
  {arm : Fin 3 → Site d}
-- given
  (hR : 1 ≤ R)
  (harmbox : ∀ i, arm i ∈ box d R)
  (harmne : ∀ i, arm i ≠ x)
  (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
  (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) :
-- imply
  ∃ t : Fin 3 → Site d, (∀ i, t i ∈ bpt_boundaryClass ω L R x (t i)) ∧ (∀ i j, i ≠ j → Disjoint (bpt_boundaryClass ω L R x (t i)) (bpt_boundaryClass ω L R x (t j))) := by
-- proof
  apply StatMech.Walls.bpt_trif_three_classes_disjoint ω L R hR arm harmbox harmne harminf harmsep

/--
[bpt_sameTrif_classes_laminar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean)
-/
@[path]
private lemma bpt_sameTrif_classes_laminar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x a b : Site d} :
-- imply
  bpt_boundaryClass ω L R x a = bpt_boundaryClass ω L R x b ∨ Disjoint (bpt_boundaryClass ω L R x a) (bpt_boundaryClass ω L R x b) := by
-- proof
  apply StatMech.Walls.bpt_sameTrif_classes_laminar ω L R x a b

/--
[bpt_cut_ground_sets_differ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean)
-/
@[path]
private lemma bpt_cut_ground_sets_differ_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  (bc57_pt ((L : ℤ) + 1) 1) ∉ bc61_boxAround 2 L (0 : Site 2) ∧ (bc57_pt ((L : ℤ) + 1) 1) ∈ bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0) := by
-- proof
  apply StatMech.Walls.bpt_cut_ground_sets_differ L hL

/--
[bpt_collapse_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean)
-/
@[path]
private lemma bpt_collapse_survives_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bpt_collapse_survives L

/--
[bpt_partitionForest_iff_bc69](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean)
-/
@[path]
private lemma bpt_partitionForest_iff_bc69_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bpt_partitionForest_iff_bc69 ω L R

/--
[bpt_count_of_partitionForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean)
-/
@[path]
private lemma bpt_count_of_partitionForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bkg_ClassicalForestData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bpt_count_of_partitionForest ω L R h

/--
[bpt_bk_of_partitionForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean)
-/
@[path]
private lemma bpt_bk_of_partitionForest_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bpt_bk_of_partitionForest p hp1 hp0 hdata

/--
[bpt_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean)
-/
@[path]
private lemma bpt_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (x : Site d) (arm : Fin 3 → Site d), (∀ i, arm i ∈ box d R) → (∀ i, arm i ≠ x) → (∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite) → (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) → ∃ t : Fin 3 → Site d, (∀ i, t i ∈ bpt_boundaryClass ω L R x (t i)) ∧ (∀ i j, i ≠ j → Disjoint (bpt_boundaryClass ω L R x (t i)) (bpt_boundaryClass ω L R x (t j)))) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (x a b : Site d), bpt_boundaryClass ω L R x a = bpt_boundaryClass ω L R x b ∨ Disjoint (bpt_boundaryClass ω L R x a) (bpt_boundaryClass ω L R x b)) ∧ (∀ (L : ℕ), 1 ≤ L → (bc57_pt ((L : ℤ) + 1) 1) ∉ bc61_boxAround 2 L (0 : Site 2) ∧ (bc57_pt ((L : ℤ) + 1) 1) ∈ bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), (bkg_ClassicalForestData ω L R ↔ bc69_Gn_globalForest ω L R) ∧ (bkg_ClassicalForestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R)) := by
-- proof
  apply StatMech.Walls.bpt_status


-- created on 2026-10-23
