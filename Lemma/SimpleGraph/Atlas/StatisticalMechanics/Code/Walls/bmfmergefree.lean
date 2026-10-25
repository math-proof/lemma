import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bmfmergefree.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bmf_o_ne_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_o_ne_a_eq :
-- imply
  (0 : Site 2) ≠ bmf_a₁ := by
-- proof
  apply StatMech.Walls.bmf_o_ne_a

/--
[bmf_o_ne_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_o_ne_a_eq_2 :
-- imply
  (0 : Site 2) ≠ bmf_a₂ := by
-- proof
  apply StatMech.Walls.bmf_o_ne_a

/--
[bmf_o_ne_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_o_ne_a_eq_3 :
-- imply
  (0 : Site 2) ≠ bmf_a₃ := by
-- proof
  apply StatMech.Walls.bmf_o_ne_a

/--
[bmf_o_ne_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_o_ne_b_eq :
-- imply
  (0 : Site 2) ≠ bmf_b₁ := by
-- proof
  apply StatMech.Walls.bmf_o_ne_b

/--
[bmf_o_ne_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_o_ne_b_eq_2 :
-- imply
  (0 : Site 2) ≠ bmf_b₂ := by
-- proof
  apply StatMech.Walls.bmf_o_ne_b

/--
[bmf_o_ne_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_o_ne_b_eq_3 :
-- imply
  (0 : Site 2) ≠ bmf_b₃ := by
-- proof
  apply StatMech.Walls.bmf_o_ne_b

/--
[bmf_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_a_eq :
-- imply
  bmf_a₁ ≠ bmf_a₂ := by
-- proof
  apply StatMech.Walls.bmf_a

/--
[bmf_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_a_eq_2 :
-- imply
  bmf_a₁ ≠ bmf_a₃ := by
-- proof
  apply StatMech.Walls.bmf_a

/--
[bmf_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_a_eq_3 :
-- imply
  bmf_a₂ ≠ bmf_a₃ := by
-- proof
  apply StatMech.Walls.bmf_a

/--
[bmf_adj_o_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_adj_o_a_eq :
-- imply
  (hypercubicLattice 2).Adj 0 bmf_a₁ := by
-- proof
  apply StatMech.Walls.bmf_adj_o_a

/--
[bmf_adj_o_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_adj_o_a_eq_2 :
-- imply
  (hypercubicLattice 2).Adj 0 bmf_a₂ := by
-- proof
  apply StatMech.Walls.bmf_adj_o_a

/--
[bmf_adj_o_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_adj_o_a_eq_3 :
-- imply
  (hypercubicLattice 2).Adj 0 bmf_a₃ := by
-- proof
  apply StatMech.Walls.bmf_adj_o_a

/--
[bmf_adj_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_adj_a_eq :
-- imply
  (hypercubicLattice 2).Adj bmf_a₁ bmf_b₁ := by
-- proof
  apply StatMech.Walls.bmf_adj_a

/--
[bmf_adj_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_adj_a_eq_2 :
-- imply
  (hypercubicLattice 2).Adj bmf_a₂ bmf_b₂ := by
-- proof
  apply StatMech.Walls.bmf_adj_a

/--
[bmf_adj_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_adj_a_eq_3 :
-- imply
  (hypercubicLattice 2).Adj bmf_a₃ bmf_b₃ := by
-- proof
  apply StatMech.Walls.bmf_adj_a

/--
[bmf_o_notMem_e](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_o_notMem_e_eq :
-- imply
  (0 : Site 2) ∉ s(bmf_a₁, bmf_b₁) := by
-- proof
  apply StatMech.Walls.bmf_o_notMem_e

/--
[bmf_o_notMem_e](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_o_notMem_e_eq_2 :
-- imply
  (0 : Site 2) ∉ s(bmf_a₂, bmf_b₂) := by
-- proof
  apply StatMech.Walls.bmf_o_notMem_e

/--
[bmf_o_notMem_e](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_o_notMem_e_eq_3 :
-- imply
  (0 : Site 2) ∉ s(bmf_a₃, bmf_b₃) := by
-- proof
  apply StatMech.Walls.bmf_o_notMem_e

/--
[bmf_corridor_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_corridor_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hω : ω ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) :
-- imply
  ω s(bmf_a₁, bmf_b₁) = true ∧ ω s(bmf_a₂, bmf_b₂) = true ∧ ω s(bmf_a₃, bmf_b₃) = true := by
-- proof
  apply StatMech.Walls.bmf_corridor_open ω hω

/--
[bmf_conn_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_conn_a_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hω : ω ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) :
-- imply
  Connected 2 (removeSite 0 ω) bmf_a₁ bmf_b₁ := by
-- proof
  apply StatMech.Walls.bmf_conn_a ω hω

/--
[bmf_conn_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_conn_a_eq_2
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hω : ω ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) :
-- imply
  Connected 2 (removeSite 0 ω) bmf_a₂ bmf_b₂ := by
-- proof
  apply StatMech.Walls.bmf_conn_a ω hω

/--
[bmf_conn_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_conn_a_eq_3
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hω : ω ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) :
-- imply
  Connected 2 (removeSite 0 ω) bmf_a₃ bmf_b₃ := by
-- proof
  apply StatMech.Walls.bmf_conn_a ω hω

/--
[bmf_hgeo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_hgeo_eq :
-- imply
  cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I)) ∩ bmf_X ⊆ NeighborTrifPrecursor 2 bmf_a₁ bmf_a₂ bmf_a₃ := by
-- proof
  apply StatMech.Walls.bmf_hgeo

/--
[bmf_precursorPos_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_precursorPos_of_residues_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hindep : bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I)) ∩ bmf_X) = bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) * bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bmf_X)
  (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bmf_X) :
-- imply
  0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (NeighborTrifPrecursor 2 bmf_a₁ bmf_a₂ bmf_a₃) := by
-- proof
  apply StatMech.Walls.bmf_precursorPos_of_residues p hp1 hp0 hplt hindep hXpos

/--
[bmf_omegaTri_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_omegaTri_true_eq
  {e : Sym2 (Site 2)} :
-- imply
  bmf_omegaTri e = true ↔ bmf_OnRay e := by
-- proof
  apply StatMech.Walls.bmf_omegaTri_true

/--
[bmf_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_R_eq
  {x : Site 2}
-- given
  (h : x ∈ bmf_R₁) :
-- imply
  x ∉ bmf_R₂ := by
-- proof
  apply StatMech.Walls.bmf_R h

/--
[bmf_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_R_eq_2
  {x : Site 2}
-- given
  (h : x ∈ bmf_R₁) :
-- imply
  x ∉ bmf_R₃ := by
-- proof
  apply StatMech.Walls.bmf_R h

/--
[bmf_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_R_eq_3
  {x : Site 2}
-- given
  (h : x ∈ bmf_R₂) :
-- imply
  x ∉ bmf_R₁ := by
-- proof
  apply StatMech.Walls.bmf_R h

/--
[bmf_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_R_eq_4
  {x : Site 2}
-- given
  (h : x ∈ bmf_R₂) :
-- imply
  x ∉ bmf_R₃ := by
-- proof
  apply StatMech.Walls.bmf_R h

/--
[bmf_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_R_eq_5
  {x : Site 2}
-- given
  (h : x ∈ bmf_R₃) :
-- imply
  x ∉ bmf_R₁ := by
-- proof
  apply StatMech.Walls.bmf_R h

/--
[bmf_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_R_eq_6
  {x : Site 2}
-- given
  (h : x ∈ bmf_R₃) :
-- imply
  x ∉ bmf_R₂ := by
-- proof
  apply StatMech.Walls.bmf_R h

/--
[bmf_walk_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_walk_invariant_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (openSubgraph 2 ω).Walk x y}
-- given
  (hclosed : ∀ x y : Site 2, x ∈ S → IsOpenEdge 2 ω x y → y ∈ S)
  (hx : x ∈ S) :
-- imply
  y ∈ S := by
-- proof
  apply StatMech.Walls.bmf_walk_invariant hclosed w hx

/--
[bmf_cluster_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_cluster_subset_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {b : Site 2}
-- given
  (hb : b ∈ S)
  (hclosed : ∀ x y : Site 2, x ∈ S → IsOpenEdge 2 ω x y → y ∈ S) :
-- imply
  cluster 2 ω b ⊆ S := by
-- proof
  apply StatMech.Walls.bmf_cluster_subset hb hclosed

/--
[bmf_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_R_eq_7
  {x y : Site 2}
-- given
  (hx : x ∈ bmf_R₁)
  (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) x y) :
-- imply
  y ∈ bmf_R₁ := by
-- proof
  apply StatMech.Walls.bmf_R x y hx hop

/--
[bmf_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_R_eq_8
  {x y : Site 2}
-- given
  (hx : x ∈ bmf_R₂)
  (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) x y) :
-- imply
  y ∈ bmf_R₂ := by
-- proof
  apply StatMech.Walls.bmf_R x y hx hop

/--
[bmf_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_R_eq_9
  {x y : Site 2}
-- given
  (hx : x ∈ bmf_R₃)
  (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) x y) :
-- imply
  y ∈ bmf_R₃ := by
-- proof
  apply StatMech.Walls.bmf_R x y hx hop

/--
[bmf_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_b_eq :
-- imply
  bmf_b₁ ∈ bmf_R₁ := by
-- proof
  apply StatMech.Walls.bmf_b

/--
[bmf_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_b_eq_2 :
-- imply
  bmf_b₂ ∈ bmf_R₂ := by
-- proof
  apply StatMech.Walls.bmf_b

/--
[bmf_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_b_eq_3 :
-- imply
  bmf_b₃ ∈ bmf_R₃ := by
-- proof
  apply StatMech.Walls.bmf_b

/--
[bmf_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_b_eq_4
  {k : ℕ} :
-- imply
  Connected 2 (removeSite 0 bmf_omegaTri) bmf_b₁ ![2 + (k : ℤ), 0] := by
-- proof
  apply StatMech.Walls.bmf_b k

/--
[bmf_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_b_eq_5 :
-- imply
  (cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₁).Infinite := by
-- proof
  apply StatMech.Walls.bmf_b

/--
[bmf_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_b_eq_6
  {k : ℕ} :
-- imply
  Connected 2 (removeSite 0 bmf_omegaTri) bmf_b₂ ![0, 2 + (k : ℤ)] := by
-- proof
  apply StatMech.Walls.bmf_b k

/--
[bmf_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_b_eq_7 :
-- imply
  (cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₂).Infinite := by
-- proof
  apply StatMech.Walls.bmf_b

/--
[bmf_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_b_eq_8
  {k : ℕ} :
-- imply
  Connected 2 (removeSite 0 bmf_omegaTri) bmf_b₃ ![-2 - (k : ℤ), 0] := by
-- proof
  apply StatMech.Walls.bmf_b k

/--
[bmf_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_b_eq_9 :
-- imply
  (cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₃).Infinite := by
-- proof
  apply StatMech.Walls.bmf_b

/--
[bmf_omegaTri_mem_X](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_omegaTri_mem_X_eq :
-- imply
  bmf_omegaTri ∈ bmf_X := by
-- proof
  apply StatMech.Walls.bmf_omegaTri_mem_X

/--
[bmf_X_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean)
-/
@[path]
private lemma bmf_X_nonempty_eq :
-- imply
  bmf_X.Nonempty := by
-- proof
  apply StatMech.Walls.bmf_X_nonempty


-- created on 2026-10-23
