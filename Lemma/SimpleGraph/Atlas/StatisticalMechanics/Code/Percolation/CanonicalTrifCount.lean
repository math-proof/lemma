import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
open Set SimpleGraph Finset StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation StatMech.Percolation.CtcWitness


/--
[ctc2_cluster_removeSite_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_cluster_removeSite_subset_eq
  {d : ℕ}
  {x a : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  cluster d (removeSite x ω) a ⊆ cluster d ω a := by
-- proof
  apply StatMech.Percolation.ctc2_cluster_removeSite_subset x a ω

/--
[ctc2_isTrifurcation_of_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_isTrifurcation_of_canonical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : IsCanonicalTrifurcation d ω x) :
-- imply
  IsTrifurcation d ω x := by
-- proof
  apply StatMech.Percolation.ctc2_isTrifurcation_of_canonical h

/--
[ctc2_arm_in_box_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_arm_in_box_succ_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a : Site d}
  {n : ℕ}
-- given
  (hx : x ∈ box d n)
  (hadj : (openSubgraph d ω).Adj x a) :
-- imply
  a ∈ box d (n + 1) := by
-- proof
  apply StatMech.Percolation.ctc2_arm_in_box_succ hx hadj

/--
[ctc2_canonical_three_disjoint_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_canonical_three_disjoint_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hxbox : x ∈ box d n)
  (htri : IsCanonicalTrifurcation d ω x) :
-- imply
  ∃ a₁ a₂ a₃ z₁ z₂ z₃ : Site d, ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧ (z₁ ∈ vertexBoundary d (n + 1) ∧ z₂ ∈ vertexBoundary d (n + 1) ∧ z₃ ∈ vertexBoundary d (n + 1)) ∧ (Connected d (removeSite x ω) a₁ z₁ ∧ Connected d (removeSite x ω) a₂ z₂ ∧ Connected d (removeSite x ω) a₃ z₃) ∧ (¬ Connected d (removeSite x ω) z₁ z₂ ∧ ¬ Connected d (removeSite x ω) z₁ z₃ ∧ ¬ Connected d (removeSite x ω) z₂ z₃) ∧ (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
-- proof
  apply StatMech.Percolation.ctc2_canonical_three_disjoint_boundary ω n hxbox htri

/--
[ctc2_armsRemoveSiteInfinite_of_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_armsRemoveSiteInfinite_of_canonical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) :
-- imply
  arc_TrifArmsRemoveSiteInfinite ω n := by
-- proof
  apply StatMech.Percolation.ctc2_armsRemoveSiteInfinite_of_canonical ω n hcanon

/--
[ctc2_count_of_armForestReaching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_count_of_armForestReaching_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : sfa_ArmForestReaching ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ctc2_count_of_armForestReaching ω n h

/--
[ctc2_count_single_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_count_single_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {c : Fin 3 → Site d}
-- given
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x)
  (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
  (hadj : ∀ i, (openSubgraph d ω).Adj x (c i))
  (hne : ∀ i, c i ≠ x)
  (hcut : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧ ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧ ¬ Connected d (removeSite x ω) (c 1) (c 2))
  (hbdry : ∀ i, c i ∈ vertexBoundary d n)
  (hinj : Function.Injective c) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ctc2_count_single_boundary ω n hxbox htri hsingle c hadj hne hcut hbdry hinj

/--
[ctc2_count_of_disjointArmEnds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_count_of_disjointArmEnds_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hdisj : bk2_DisjointArmEnds ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ctc2_count_of_disjointArmEnds ω n hn hdisj

/--
[ctc2_count_of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_count_of_subsingleton_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n → IsTrifurcation d ω y → x = y) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ctc2_count_of_subsingleton ω n hn hsub

/--
[ctc2_count_of_forestLeafInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_count_of_forestLeafInjection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daec_ForestLeafInjection ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ctc2_count_of_forestLeafInjection ω n h

/--
[ctc2_canonTcount_le_Tcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_canonTcount_le_Tcount_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  ctc2_canonTcount d ω n ≤ Tcount d ω n := by
-- proof
  apply StatMech.Percolation.ctc2_canonTcount_le_Tcount ω n

/--
[ctc2_canonTcount_le_boundary_of_forestLeafInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_canonTcount_le_boundary_of_forestLeafInjection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daec_ForestLeafInjection ω n) :
-- imply
  ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ctc2_canonTcount_le_boundary_of_forestLeafInjection ω n h

/--
[ctc2_canonTcount_le_boundary_of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_canonTcount_le_boundary_of_subsingleton_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n → IsTrifurcation d ω y → x = y) :
-- imply
  ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.ctc2_canonTcount_le_boundary_of_subsingleton ω n hn hsub

/--
[px_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma px_inj_eq
  {d : ℕ} :
-- imply
  Function.Injective px := by
-- proof
  apply StatMech.Percolation.CtcWitness.px_inj

/--
[py_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma py_inj_eq
  {d : ℕ} :
-- imply
  Function.Injective py := by
-- proof
  apply StatMech.Percolation.CtcWitness.py_inj

/--
[px_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma px_adj_eq
  {d : ℕ}
  {k : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (px k) (px (k + 1)) := by
-- proof
  apply StatMech.Percolation.CtcWitness.px_adj k

/--
[py_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma py_adj_eq
  {d : ℕ}
  {k : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (py k) (py (k + 1)) := by
-- proof
  apply StatMech.Percolation.CtcWitness.py_adj k

/--
[px_ray_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma px_ray_open_eq
  {d : ℕ}
  {k : ℤ} :
-- imply
  threeRayConfig s(px k, px (k + 1)) = true := by
-- proof
  apply StatMech.Percolation.CtcWitness.px_ray_open k

/--
[px_zero_eq_py_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma px_zero_eq_py_zero_eq
  {d : ℕ} :
-- imply
  px 0 = py 0 := by
-- proof
  apply StatMech.Percolation.CtcWitness.px_zero_eq_py_zero

/--
[py_ray_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma py_ray_open_eq
  {d : ℕ}
  {k : ℤ}
-- given
  (hk : 0 ≤ k) :
-- imply
  threeRayConfig s(py k, py (k + 1)) = true := by
-- proof
  apply StatMech.Percolation.CtcWitness.py_ray_open k hk

/--
[cut_px_pos_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_px_pos_open_eq
  {d : ℕ}
  {k : ℤ}
-- given
  (hk : 1 ≤ k) :
-- imply
  (removeSite (px 0) threeRayConfig) s(px k, px (k + 1)) = true := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_px_pos_open k hk

/--
[cut_px_neg_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_px_neg_open_eq
  {d : ℕ}
  {k : ℤ}
-- given
  (hk : k ≤ -2) :
-- imply
  (removeSite (px 0) threeRayConfig) s(px k, px (k + 1)) = true := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_px_neg_open k hk

/--
[cut_py_pos_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_py_pos_open_eq
  {d : ℕ}
  {k : ℤ}
-- given
  (hk : 1 ≤ k) :
-- imply
  (removeSite (px 0) threeRayConfig) s(py k, py (k + 1)) = true := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_py_pos_open k hk

/--
[cut_connected_px_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_connected_px_pos_eq
  {d : ℕ}
  {m : ℤ}
-- given
  (hm : 1 ≤ m) :
-- imply
  Connected 2 (removeSite (px 0) threeRayConfig) (px 1) (px m) := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_connected_px_pos m hm

/--
[cut_connected_px_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_connected_px_neg_eq
  {d : ℕ}
  {m : ℤ}
-- given
  (hm : 1 ≤ m) :
-- imply
  Connected 2 (removeSite (px 0) threeRayConfig) (px (-1)) (px (-m)) := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_connected_px_neg m hm

/--
[cut_connected_py_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_connected_py_pos_eq
  {d : ℕ}
  {m : ℤ}
-- given
  (hm : 1 ≤ m) :
-- imply
  Connected 2 (removeSite (px 0) threeRayConfig) (py 1) (py m) := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_connected_py_pos m hm

/--
[px_pos_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma px_pos_outside_box_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  px (n + 1) ∉ box 2 n := by
-- proof
  apply StatMech.Percolation.CtcWitness.px_pos_outside_box n

/--
[px_neg_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma px_neg_outside_box_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  px (-(n + 1 : ℤ)) ∉ box 2 n := by
-- proof
  apply StatMech.Percolation.CtcWitness.px_neg_outside_box n

/--
[py_pos_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma py_pos_outside_box_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  py (n + 1) ∉ box 2 n := by
-- proof
  apply StatMech.Percolation.CtcWitness.py_pos_outside_box n

/--
[cut_px_pos_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_px_pos_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 (removeSite (px 0) threeRayConfig) (px 1)).Infinite := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_px_pos_infinite

/--
[cut_px_neg_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_px_neg_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 (removeSite (px 0) threeRayConfig) (px (-1))).Infinite := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_px_neg_infinite

/--
[cut_py_pos_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_py_pos_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 (removeSite (px 0) threeRayConfig) (py 1)).Infinite := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_py_pos_infinite

/--
[cut_edge_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_edge_classify_eq
  {d : ℕ}
  {a b : Site 2}
-- given
  (hopen : (removeSite (px 0) threeRayConfig) s(a, b) = true) :
-- imply
  (∃ k : ℤ, 1 ≤ k ∧ s(a, b) = s(px k, px (k + 1))) ∨ (∃ k : ℤ, k ≤ -2 ∧ s(a, b) = s(px k, px (k + 1))) ∨ (∃ k : ℤ, 1 ≤ k ∧ s(a, b) = s(py k, py (k + 1))) := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_edge_classify hopen

/--
[px_edge_coords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma px_edge_coords_eq
  {d : ℕ}
  {u v : Site 2}
  {k : ℤ}
-- given
  (he : (u = px k ∧ v = px (k + 1)) ∨ (u = px (k + 1) ∧ v = px k)) :
-- imply
  (u 0 = k ∧ v 0 = k + 1 ∨ u 0 = k + 1 ∧ v 0 = k) ∧ u 1 = 0 ∧ v 1 = 0 := by
-- proof
  apply StatMech.Percolation.CtcWitness.px_edge_coords he

/--
[py_edge_coords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma py_edge_coords_eq
  {d : ℕ}
  {u v : Site 2}
  {k : ℤ}
-- given
  (he : (u = py k ∧ v = py (k + 1)) ∨ (u = py (k + 1) ∧ v = py k)) :
-- imply
  u 0 = 0 ∧ v 0 = 0 ∧ (u 1 = k ∧ v 1 = k + 1 ∨ u 1 = k + 1 ∧ v 1 = k) := by
-- proof
  apply StatMech.Percolation.CtcWitness.py_edge_coords he

/--
[cut_px_pos_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_px_pos_step_eq
  {d : ℕ}
  {u v : Site 2}
-- given
  (hu : 1 ≤ u 0 ∧ u 1 = 0)
  (hadj : (openSubgraph 2 (removeSite (px 0) threeRayConfig)).Adj u v) :
-- imply
  1 ≤ v 0 ∧ v 1 = 0 := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_px_pos_step hu hadj

/--
[cut_px_pos_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_px_pos_invariant_eq
  {d : ℕ}
  {u y : Site 2}
-- given
  (hu : 1 ≤ u 0 ∧ u 1 = 0)
  (h : Connected 2 (removeSite (px 0) threeRayConfig) u y) :
-- imply
  1 ≤ y 0 ∧ y 1 = 0 := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_px_pos_invariant hu h

/--
[cut_px_neg_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_px_neg_step_eq
  {d : ℕ}
  {u v : Site 2}
-- given
  (hu : u 0 ≤ -1 ∧ u 1 = 0)
  (hadj : (openSubgraph 2 (removeSite (px 0) threeRayConfig)).Adj u v) :
-- imply
  v 0 ≤ -1 ∧ v 1 = 0 := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_px_neg_step hu hadj

/--
[cut_px_neg_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_px_neg_invariant_eq
  {d : ℕ}
  {u y : Site 2}
-- given
  (hu : u 0 ≤ -1 ∧ u 1 = 0)
  (h : Connected 2 (removeSite (px 0) threeRayConfig) u y) :
-- imply
  y 0 ≤ -1 ∧ y 1 = 0 := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_px_neg_invariant hu h

/--
[cut_py_pos_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_py_pos_step_eq
  {d : ℕ}
  {u v : Site 2}
-- given
  (hu : u 0 = 0 ∧ 1 ≤ u 1)
  (hadj : (openSubgraph 2 (removeSite (px 0) threeRayConfig)).Adj u v) :
-- imply
  v 0 = 0 ∧ 1 ≤ v 1 := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_py_pos_step hu hadj

/--
[cut_py_pos_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_py_pos_invariant_eq
  {d : ℕ}
  {u y : Site 2}
-- given
  (hu : u 0 = 0 ∧ 1 ≤ u 1)
  (h : Connected 2 (removeSite (px 0) threeRayConfig) u y) :
-- imply
  y 0 = 0 ∧ 1 ≤ y 1 := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_py_pos_invariant hu h

/--
[cut_disconnect_pos_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_disconnect_pos_neg_eq
  {d : ℕ} :
-- imply
  ¬ Connected 2 (removeSite (px 0) threeRayConfig) (px 1) (px (-1)) := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_disconnect_pos_neg

/--
[cut_disconnect_pos_py](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_disconnect_pos_py_eq
  {d : ℕ} :
-- imply
  ¬ Connected 2 (removeSite (px 0) threeRayConfig) (px 1) (py 1) := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_disconnect_pos_py

/--
[cut_disconnect_neg_py](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma cut_disconnect_neg_py_eq
  {d : ℕ} :
-- imply
  ¬ Connected 2 (removeSite (px 0) threeRayConfig) (px (-1)) (py 1) := by
-- proof
  apply StatMech.Percolation.CtcWitness.cut_disconnect_neg_py

/--
[ctc2_isCanonicalTrifurcation_threeRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean)
-/
@[path]
private lemma ctc2_isCanonicalTrifurcation_threeRay_eq
  {d : ℕ} :
-- imply
  ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2), IsCanonicalTrifurcation 2 ω x := by
-- proof
  apply StatMech.Percolation.ctc2_isCanonicalTrifurcation_threeRay


-- created on 2026-10-23
