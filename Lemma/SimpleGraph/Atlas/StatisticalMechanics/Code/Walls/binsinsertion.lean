import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.binsinsertion
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Ising StatMech.IsingFK StatMech.Walls


/--
[bins_cluster_subset_of_openClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_cluster_subset_of_openClosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
  {S : Set (Site 2)}
-- given
  (ha : a ∈ S)
  (hclosed : ∀ u v : Site 2, u ∈ S → IsOpenEdge 2 (removeSite 0 ω) u v → v ∈ S) :
-- imply
  cluster 2 (removeSite 0 ω) a ⊆ S := by
-- proof
  apply StatMech.Walls.bins_cluster_subset_of_openClosed ω ha hclosed

/--
[bins_precursor_of_sides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_precursor_of_sides_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a₁ a₂ a₃ : Site 2}
  {S₁ S₂ S₃ : Set (Site 2)}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧ (hypercubicLattice 2).Adj 0 a₃)
  (ha : a₁ ∈ S₁ ∧ a₂ ∈ S₂ ∧ a₃ ∈ S₃)
  (hd : Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃)
  (hc : (∀ u v : Site 2, u ∈ S₁ → IsOpenEdge 2 (removeSite 0 ω) u v → v ∈ S₁) ∧ (∀ u v : Site 2, u ∈ S₂ → IsOpenEdge 2 (removeSite 0 ω) u v → v ∈ S₂) ∧ (∀ u v : Site 2, u ∈ S₃ → IsOpenEdge 2 (removeSite 0 ω) u v → v ∈ S₃))
  (hinf : (cluster 2 (removeSite 0 ω) a₁).Infinite ∧ (cluster 2 (removeSite 0 ω) a₂).Infinite ∧ (cluster 2 (removeSite 0 ω) a₃).Infinite) :
-- imply
  ω ∈ NeighborTrifPrecursor 2 a₁ a₂ a₃ := by
-- proof
  apply StatMech.Walls.bins_precursor_of_sides ω a₁ a₂ a₃ hne hadj S₁ S₂ S₃ ha hd hc hinf

/--
[bins_ExtEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_ExtEvent_dependsOn_eq
  {I : Finset (Sym2 (Site 2))}
  {u₁ u₂ u₃ : Site 2} :
-- imply
  DependsOn (bins_ExtEvent I u₁ u₂ u₃) ((↑I : Set (Sym2 (Site 2)))ᶜ) := by
-- proof
  apply StatMech.Walls.bins_ExtEvent_dependsOn I u₁ u₂ u₃

/--
[bins_measurable_closeI](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_measurable_closeI_eq
  {I : Finset (Sym2 (Site 2))} :
-- imply
  Measurable (fun ω : ConfigSpace (Sym2 (Site 2)) ↦ bpt2_closeI I ω) := by
-- proof
  apply StatMech.Walls.bins_measurable_closeI I

/--
[bins_ExtEvent_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_ExtEvent_measurable_eq
  {I : Finset (Sym2 (Site 2))}
  {u₁ u₂ u₃ : Site 2} :
-- imply
  MeasurableSet (bins_ExtEvent I u₁ u₂ u₃) := by
-- proof
  apply StatMech.Walls.bins_ExtEvent_measurable I u₁ u₂ u₃

/--
[bins_exists_ExtEvent_pos_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_exists_ExtEvent_pos_of_cover_eq
  {n : ℕ}
  {I : Finset (Sym2 (Site 2))}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n))
  (hcover : threeMeetBox 2 n ⊆ ⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2, bins_ExtEvent I u₁ u₂ u₃) :
-- imply
  ∃ u₁ u₂ u₃ : Site 2, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bins_ExtEvent I u₁ u₂ u₃) := by
-- proof
  apply StatMech.Walls.bins_exists_ExtEvent_pos_of_cover p hp1 n I hpos hcover

/--
[bins_openSubgraph_closeTouch_eq_removeBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_openSubgraph_closeTouch_eq_removeBox_eq
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  openSubgraph 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω)) = openSubgraph 2 (removeSites (boxFinset 2 n) ω) := by
-- proof
  apply StatMech.Walls.bins_openSubgraph_closeTouch_eq_removeBox n ω

/--
[bins_cluster_closeTouch_eq_removeBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_cluster_closeTouch_eq_removeBox_eq
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {u : Site 2} :
-- imply
  cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) ω)) u = cluster 2 (removeSites (boxFinset 2 n) ω) u := by
-- proof
  apply StatMech.Walls.bins_cluster_closeTouch_eq_removeBox n ω u

/--
[bins_threeMeetBox_subset_iUnion_ExtEvent_touch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_threeMeetBox_subset_iUnion_ExtEvent_touch_eq
  {n : ℕ} :
-- imply
  threeMeetBox 2 n ⊆ ⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2, bins_ExtEvent (bondFinsetTouch 2 n) u₁ u₂ u₃ := by
-- proof
  apply StatMech.Walls.bins_threeMeetBox_subset_iUnion_ExtEvent_touch n

/--
[bins_exists_ExtEvent_touch_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_exists_ExtEvent_touch_pos_eq
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n)) :
-- imply
  ∃ u₁ u₂ u₃ : Site 2, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bins_ExtEvent (bondFinsetTouch 2 n) u₁ u₂ u₃) := by
-- proof
  apply StatMech.Walls.bins_exists_ExtEvent_touch_pos p hp1 n hpos

/--
[bins_ShellExtEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_ShellExtEvent_dependsOn_eq
  {n : ℕ}
  {v₁ v₂ v₃ u₁ u₂ u₃ : Site 2} :
-- imply
  DependsOn (bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃) ((↑(bondFinsetTouch 2 n) : Set (Sym2 (Site 2)))ᶜ) := by
-- proof
  apply StatMech.Walls.bins_ShellExtEvent_dependsOn n v₁ v₂ v₃ u₁ u₂ u₃

/--
[bins_ShellExtEvent_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_ShellExtEvent_measurable_eq
  {n : ℕ}
  {v₁ v₂ v₃ u₁ u₂ u₃ : Site 2} :
-- imply
  MeasurableSet (bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃) := by
-- proof
  apply StatMech.Walls.bins_ShellExtEvent_measurable n v₁ v₂ v₃ u₁ u₂ u₃

/--
[bins_threeMeetBox_subset_iUnion_ShellExtEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_threeMeetBox_subset_iUnion_ShellExtEvent_eq
  {n : ℕ} :
-- imply
  threeMeetBox 2 n ⊆ ⋃ v₁ : Site 2, ⋃ v₂ : Site 2, ⋃ v₃ : Site 2, ⋃ u₁ : Site 2, ⋃ u₂ : Site 2, ⋃ u₃ : Site 2, bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃ := by
-- proof
  apply StatMech.Walls.bins_threeMeetBox_subset_iUnion_ShellExtEvent n

/--
[bins_exists_ShellExtEvent_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_exists_ShellExtEvent_pos_eq
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n)) :
-- imply
  ∃ v₁ v₂ v₃ u₁ u₂ u₃ : Site 2, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bins_ShellExtEvent n v₁ v₂ v₃ u₁ u₂ u₃) := by
-- proof
  apply StatMech.Walls.bins_exists_ShellExtEvent_pos p hp1 n hpos

/--
[bins_iEqTop_subset_iUnion_NineMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_iEqTop_subset_iUnion_NineMeetBox_eq :
-- imply
  {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} ⊆ ⋃ n, bins_NineMeetBox n := by
-- proof
  apply StatMech.Walls.bins_iEqTop_subset_iUnion_NineMeetBox

/--
[bins_exists_NineMeetBox_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_exists_NineMeetBox_pos_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (htop : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = ⊤}) :
-- imply
  ∃ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bins_NineMeetBox n) := by
-- proof
  apply StatMech.Walls.bins_exists_NineMeetBox_pos p hp1 htop

/--
[bins_NineMeetBox_subset_iUnion_NineShellEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_NineMeetBox_subset_iUnion_NineShellEvent_eq
  {n : ℕ} :
-- imply
  bins_NineMeetBox n ⊆ ⋃ v : Fin 9 → Site 2, ⋃ u : Fin 9 → Site 2, bins_NineShellEvent n v u := by
-- proof
  apply StatMech.Walls.bins_NineMeetBox_subset_iUnion_NineShellEvent n

/--
[bins_exists_NineShellEvent_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_exists_NineShellEvent_pos_eq
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bins_NineMeetBox n)) :
-- imply
  ∃ (v u : Fin 9 → Site 2), 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bins_NineShellEvent n v u) := by
-- proof
  apply StatMech.Walls.bins_exists_NineShellEvent_pos p hp1 n hpos

/--
[bins_exists_NineShellEvent_pos_of_threeMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_exists_NineShellEvent_pos_of_threeMeetBox_eq
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n)) :
-- imply
  ∃ (m : ℕ) (v u : Fin 9 → Site 2), 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bins_NineShellEvent m v u) := by
-- proof
  apply StatMech.Walls.bins_exists_NineShellEvent_pos_of_threeMeetBox p hp1 n hpos

/--
[bins_outside_neighbor_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_outside_neighbor_side_eq
  {n : ℕ}
  {v u : Site 2}
-- given
  (hv : v ∈ box 2 n)
  (hadj : (hypercubicLattice 2).Adj v u)
  (hu : u ∉ box 2 n) :
-- imply
  u 0 = (n : ℤ) + 1 ∨ u 0 = -((n : ℤ) + 1) ∨ u 1 = (n : ℤ) + 1 ∨ u 1 = -((n : ℤ) + 1) := by
-- proof
  apply StatMech.Walls.bins_outside_neighbor_side hv hadj hu

/--
[bins_v_coord_of_outSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_v_coord_of_outSide_eq
  {n : ℕ}
  {v u : Site 2}
-- given
  (hv : v ∈ box 2 n)
  (hadj : (hypercubicLattice 2).Adj v u)
  (hu : u ∉ box 2 n) :
-- imply
  (bins_outSide n u = 0 → v 0 = (n : ℤ)) ∧ (bins_outSide n u = 1 → v 0 = -(n : ℤ)) ∧ (bins_outSide n u = 2 → v 1 = (n : ℤ)) ∧ (bins_outSide n u = 3 → v 1 = -(n : ℤ)) := by
-- proof
  apply StatMech.Walls.bins_v_coord_of_outSide hv hadj hu

/--
[bins_u_coord_of_outSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_u_coord_of_outSide_eq
  {n : ℕ}
  {v u : Site 2}
-- given
  (hv : v ∈ box 2 n)
  (hadj : (hypercubicLattice 2).Adj v u)
  (hu : u ∉ box 2 n) :
-- imply
  (bins_outSide n u = 0 → u 0 = (n : ℤ) + 1 ∧ u 1 = v 1) ∧ (bins_outSide n u = 1 → u 0 = -((n : ℤ) + 1) ∧ u 1 = v 1) ∧ (bins_outSide n u = 2 → u 0 = v 0 ∧ u 1 = (n : ℤ) + 1) ∧ (bins_outSide n u = 3 → u 0 = v 0 ∧ u 1 = -((n : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bins_u_coord_of_outSide hv hadj hu

/--
[bins_NineShellEvent_three_same_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_NineShellEvent_three_same_side_eq
  {n : ℕ}
  {v u : Fin 9 → Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hE : ω ∈ bins_NineShellEvent n v u) :
-- imply
  ∃ i j k : Fin 9, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ v i ≠ v j ∧ v i ≠ v k ∧ v j ≠ v k ∧ ((v i 0 = (n : ℤ) ∧ v j 0 = (n : ℤ) ∧ v k 0 = (n : ℤ)) ∨ (v i 0 = -(n : ℤ) ∧ v j 0 = -(n : ℤ) ∧ v k 0 = -(n : ℤ)) ∨ (v i 1 = (n : ℤ) ∧ v j 1 = (n : ℤ) ∧ v k 1 = (n : ℤ)) ∨ (v i 1 = -(n : ℤ) ∧ v j 1 = -(n : ℤ) ∧ v k 1 = -(n : ℤ))) := by
-- proof
  apply StatMech.Walls.bins_NineShellEvent_three_same_side hE

/--
[bins_routePackage_of_corridors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_routePackage_of_corridors_eq
  {m : ℕ}
  {u₁ u₂ u₃ : Site 2}
  {I : Finset (Sym2 (Site 2))}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hu₁ : u₁ ≠ ![0, 0])
  (hu₂ : u₂ ≠ ![0, 0])
  (hu₃ : u₃ ≠ ![0, 0])
  (hC : bcor_Corridors m u₁ u₂ u₃)
  (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bins_ExtEvent I u₁ u₂ u₃))
  (hpattern : ∀ a₁ a₂ a₃ : Site 2, ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧ (hypercubicLattice 2).Adj 0 a₃) → (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) → ∃ η₀ : ConfigSpace ↥I, cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ bins_ExtEvent I u₁ u₂ u₃ ⊆ NeighborTrifPrecursor 2 a₁ a₂ a₃) :
-- imply
  ∃ (η₀ : ConfigSpace ↥I) (a₁ a₂ a₃ : Site 2) (X : Set (ConfigSpace (Sym2 (Site 2)))), (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧ (hypercubicLattice 2).Adj 0 a₃) ∧ MeasurableSet X ∧ DependsOn X ((↑I : Set (Sym2 (Site 2)))ᶜ) ∧ 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 X ∧ cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ X ⊆ NeighborTrifPrecursor 2 a₁ a₂ a₃ := by
-- proof
  apply StatMech.Walls.bins_routePackage_of_corridors p hp1 m u₁ u₂ u₃ I hu₁ hu₂ hu₃ hC hXpos hpattern

/--
[bins_hroute_of_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_hroute_of_route_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hres : bins_Route p hp1) :
-- imply
  ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) → ∃ a₁ a₂ a₃ : Site 2, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bins_hroute_of_route p hp1 hp0 hplt hres

/--
[bins_bk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_bk_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hres : bins_Route p hp1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bins_bk p hp1 hp0 hplt hres

/--
[bins_bk_atLeastTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean)
-/
@[path]
private lemma bins_bk_atLeastTwo_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hres : bins_Route p hp1) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bins_bk_atLeastTwo p hp1 hp0 hplt hres


-- created on 2026-10-23
