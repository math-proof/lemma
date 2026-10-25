import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.binsclosure.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Ising StatMech.IsingFK StatMech.Walls


/--
[bins_connected_of_walk_edges_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_connected_of_walk_edges_open_eq
  {x y : Site 2}
  {P : (hypercubicLattice 2).Walk x y}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hopen : forall e, e ∈ P.edges -> omega e = true) :
-- imply
  Connected 2 omega x y := by
-- proof
  apply StatMech.Walls.bins_connected_of_walk_edges_open P omega hopen

/--
[bins_cylinder_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_cylinder_value_eq
  {I : Finset (Sym2 (Site 2))}
  {eta : ConfigSpace (Subtype fun e => e ∈ I)}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)}
-- given
  (hcyl : omega ∈ cylinder I ({eta} : Set (ConfigSpace (Subtype fun e => e ∈ I))))
  (he : e ∈ I) :
-- imply
  omega e = eta ⟨e, he⟩ := by
-- proof
  apply StatMech.Walls.bins_cylinder_value hcyl e he

/--
[bins_corridors_of_same_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_corridors_of_same_side_eq
  {n : ℕ}
  {v1 v2 v3 : Site 2}
-- given
  (hn : 1 ≤ n)
  (hv1 : v1 ∈ box 2 n)
  (hv2 : v2 ∈ box 2 n)
  (hv3 : v3 ∈ box 2 n)
  (h12 : v1 ≠ v2)
  (h13 : v1 ≠ v3)
  (h23 : v2 ≠ v3)
  (hside : (v1 0 = (n : ℤ) ∧ v2 0 = (n : ℤ) ∧ v3 0 = (n : ℤ)) ∨ (v1 0 = -(n : ℤ) ∧ v2 0 = -(n : ℤ) ∧ v3 0 = -(n : ℤ)) ∨ (v1 1 = (n : ℤ) ∧ v2 1 = (n : ℤ) ∧ v3 1 = (n : ℤ)) ∨ (v1 1 = -(n : ℤ) ∧ v2 1 = -(n : ℤ) ∧ v3 1 = -(n : ℤ))) :
-- imply
  bcor_Corridors n v1 v2 v3 := by
-- proof
  apply StatMech.Walls.bins_corridors_of_same_side n hn v1 v2 v3 hv1 hv2 hv3 h12 h13 h23 hside

/--
[bins_walk_edge_mem_touch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_walk_edge_mem_touch_eq
  {n : ℕ}
  {x y : Site 2}
  {P : (hypercubicLattice 2).Walk x y}
-- given
  (hbox : ∀ z ∈ P.support, z ∈ box 2 n) :
-- imply
  P.edges.toFinset ⊆ bondFinsetTouch 2 n := by
-- proof
  apply StatMech.Walls.bins_walk_edge_mem_touch P hbox

/--
[bins_extCluster_avoids_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_extCluster_avoids_box_eq
  {n : ℕ}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u : Site 2}
-- given
  (hu : u ∉ box 2 n) :
-- imply
  Disjoint (cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) u) (box 2 n) := by
-- proof
  apply StatMech.Walls.bins_extCluster_avoids_box n omega u hu

/--
[bins_touchPattern_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_touchPattern_value_eq
  {n : ℕ}
  {B : Fin 3 → bins_Branch}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)}
-- given
  (hcyl : omega ∈ cylinder (bondFinsetTouch 2 n) ({bins_touchPattern n B} : Set (ConfigSpace (Subtype fun e => e ∈ bondFinsetTouch 2 n))))
  (he : e ∈ bondFinsetTouch 2 n) :
-- imply
  omega e = true ↔ e ∈ bins_branchEdges B := by
-- proof
  apply StatMech.Walls.bins_touchPattern_value hcyl he

/--
[bins_tail_connected_remove_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_tail_connected_remove_start_eq
  {x v : Site 2}
  {P : (hypercubicLattice 2).Walk x v}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hp : P.IsPath)
  (hv : v ≠ x)
  (hopen : ∀ e ∈ P.edges, omega e = true) :
-- imply
  Connected 2 (removeSite x omega) P.snd v := by
-- proof
  apply StatMech.Walls.bins_tail_connected_remove_start P hp hv omega hopen

/--
[bins_branch_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_branch_connected_eq
  {n : ℕ}
  {B : Fin 3 → bins_Branch}
  {i : Fin 3}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hp : (B i).P.IsPath)
  (hv : (B i).v ≠ ![0, 0])
  (hadj : (hypercubicLattice 2).Adj (B i).v (B i).u)
  (hu : (B i).u ≠ ![0, 0])
  (hcyl : omega ∈ cylinder (bondFinsetTouch 2 n) ({bins_touchPattern n B} : Set (ConfigSpace (Subtype fun e => e ∈ bondFinsetTouch 2 n))))
  (hbox : ∀ z ∈ (B i).P.support, z ∈ box 2 n) :
-- imply
  Connected 2 (removeSite 0 omega) (B i).P.snd (B i).u := by
-- proof
  apply StatMech.Walls.bins_branch_connected i hp hv hadj hu hcyl hbox

/--
[bins_branchSide_openClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_branchSide_openClosed_eq
  {n : ℕ}
  {B : Fin 3 → bins_Branch}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {i : Fin 3}
-- given
  (hbox : ∀ i z, z ∈ (B i).P.support → z ∈ box 2 n)
  (hpathDisj : ∀ i j, i ≠ j → ∀ z, z ∈ (B i).P.support → z ∈ (B j).P.support → z = ![0, 0])
  (hadj : ∀ i, (hypercubicLattice 2).Adj (B i).v (B i).u)
  (huout : ∀ i, (B i).u ∉ box 2 n)
  (hcyl : omega ∈ cylinder (bondFinsetTouch 2 n) ({bins_touchPattern n B} : Set (ConfigSpace (Subtype fun e => e ∈ bondFinsetTouch 2 n))))
  (hclusterNe : ∀ i j, i ≠ j → cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B i).u ≠ cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B j).u) :
-- imply
  ∀ z w : Site 2, z ∈ bins_branchSide (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B i) → IsOpenEdge 2 (removeSite 0 omega) z w → w ∈ bins_branchSide (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B i) := by
-- proof
  apply StatMech.Walls.bins_branchSide_openClosed hbox hpathDisj hadj huout hcyl hclusterNe i

/--
[bins_snd_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_snd_data_eq
  {x v : Site 2}
  {P : (hypercubicLattice 2).Walk x v}
-- given
  (hp : P.IsPath)
  (hv : v ≠ x) :
-- imply
  (hypercubicLattice 2).Adj x P.snd ∧ P.snd ∈ P.support ∧ P.snd ≠ x := by
-- proof
  apply StatMech.Walls.bins_snd_data P hp hv

/--
[bins_branchSide_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_branchSide_disjoint_eq
  {n : ℕ}
  {B : Fin 3 → bins_Branch}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {i j : Fin 3}
-- given
  (hbox : ∀ i z, z ∈ (B i).P.support → z ∈ box 2 n)
  (hpathDisj : ∀ i j, i ≠ j → ∀ z, z ∈ (B i).P.support → z ∈ (B j).P.support → z = ![0, 0])
  (huout : ∀ i, (B i).u ∉ box 2 n)
  (hclusterNe : ∀ i j, i ≠ j → cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B i).u ≠ cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B j).u)
  (hij : i ≠ j) :
-- imply
  Disjoint (bins_branchSide (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B i)) (bins_branchSide (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B j)) := by
-- proof
  apply StatMech.Walls.bins_branchSide_disjoint hbox hpathDisj huout hclusterNe hij

/--
[bins_pattern_of_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_pattern_of_branches_eq
  {n : ℕ}
  {B : Fin 3 → bins_Branch}
-- given
  (hp : ∀ i, (B i).P.IsPath)
  (hv : ∀ i, (B i).v ≠ ![0, 0])
  (hbox : ∀ i z, z ∈ (B i).P.support → z ∈ box 2 n)
  (hpathDisj : ∀ i j, i ≠ j → ∀ z, z ∈ (B i).P.support → z ∈ (B j).P.support → z = ![0, 0])
  (hadj : ∀ i, (hypercubicLattice 2).Adj (B i).v (B i).u)
  (huout : ∀ i, (B i).u ∉ box 2 n) :
-- imply
  cylinder (bondFinsetTouch 2 n) ({bins_touchPattern n B} : Set (ConfigSpace (Subtype fun e => e ∈ bondFinsetTouch 2 n))) ∩ bins_ExtEvent (bondFinsetTouch 2 n) (B 0).u (B 1).u (B 2).u ⊆ NeighborTrifPrecursor 2 (B 0).P.snd (B 1).P.snd (B 2).P.snd := by
-- proof
  apply StatMech.Walls.bins_pattern_of_branches B hp hv hbox hpathDisj hadj huout

/--
[bins_routePackage_of_nineShell_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_routePackage_of_nineShell_measure_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  {m : ℕ}
  {v u : Fin 9 → Site 2}
-- given
  (hpos : 0 < mu (bins_NineShellEvent m v u)) :
-- imply
  ∃ (I : Finset (Sym2 (Site 2))) (eta : ConfigSpace ↥I) (a1 a2 a3 : Site 2) (X : Set (ConfigSpace (Sym2 (Site 2)))), (a1 ≠ a2 ∧ a1 ≠ a3 ∧ a2 ≠ a3) ∧ ((hypercubicLattice 2).Adj 0 a1 ∧ (hypercubicLattice 2).Adj 0 a2 ∧ (hypercubicLattice 2).Adj 0 a3) ∧ MeasurableSet X ∧ DependsOn X ((↑I : Set (Sym2 (Site 2)))ᶜ) ∧ 0 < mu X ∧ cylinder I ({eta} : Set (ConfigSpace ↥I)) ∩ X ⊆ NeighborTrifPrecursor 2 a1 a2 a3 := by
-- proof
  apply StatMech.Walls.bins_routePackage_of_nineShell_measure mu m v u hpos

/--
[bins_routePackage_of_nineShell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_routePackage_of_nineShell_eq
  {m : ℕ}
  {v u : Fin 9 → Site 2}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bins_NineShellEvent m v u)) :
-- imply
  ∃ (I : Finset (Sym2 (Site 2))) (eta : ConfigSpace ↥I) (a1 a2 a3 : Site 2) (X : Set (ConfigSpace (Sym2 (Site 2)))), (a1 ≠ a2 ∧ a1 ≠ a3 ∧ a2 ≠ a3) ∧ ((hypercubicLattice 2).Adj 0 a1 ∧ (hypercubicLattice 2).Adj 0 a2 ∧ (hypercubicLattice 2).Adj 0 a3) ∧ MeasurableSet X ∧ DependsOn X ((↑I : Set (Sym2 (Site 2)))ᶜ) ∧ 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 X ∧ cylinder I ({eta} : Set (ConfigSpace ↥I)) ∩ X ⊆ NeighborTrifPrecursor 2 a1 a2 a3 := by
-- proof
  apply StatMech.Walls.bins_routePackage_of_nineShell p hp1 m v u hpos

/--
[bins_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_route_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1) :
-- imply
  bins_Route p hp1 := by
-- proof
  apply StatMech.Walls.bins_route p hp1

/--
[bins_bk_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean)
-/
@[path]
private lemma bins_bk_unconditional_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {omega | numInfiniteClusters 2 omega = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {omega | numInfiniteClusters 2 omega = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {omega | numInfiniteClusters 2 omega ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bins_bk_unconditional p hp1 hp0 hplt


-- created on 2026-10-23
