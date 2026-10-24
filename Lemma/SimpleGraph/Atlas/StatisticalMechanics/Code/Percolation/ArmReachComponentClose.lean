import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.ArmReachComponentClose
open Set SimpleGraph Finset StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[arc_x_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_x_isolated_eq
  {d : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d} :
-- imply
  ¬ (openSubgraph d (removeSite x ω)).Adj x y := by
-- proof
  apply StatMech.Percolation.arc_x_isolated x ω y

/--
[arc_walk_avoids_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_walk_avoids_x_eq
  {d : ℕ}
  {x a b : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : (openSubgraph d (removeSite x ω)).Walk a b}
-- given
  (hax : a ≠ x) :
-- imply
  x ∉ w.support := by
-- proof
  apply StatMech.Percolation.arc_walk_avoids_x hax w

/--
[arc_infinite_cluster_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_infinite_cluster_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a : Site d}
-- given
  (hn : 1 ≤ n)
  (hax : a ≠ x)
  (habox : a ∈ box d n)
  (hinf : (cluster d (removeSite x ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d n, ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, x ∉ w.support := by
-- proof
  apply StatMech.Percolation.arc_infinite_cluster_reaches_boundary ω n hn x a hax habox hinf

/--
[arc_connected_removeSite_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_connected_removeSite_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a : Site d}
-- given
  (hn : 1 ≤ n)
  (hax : a ≠ x)
  (habox : a ∈ box d n)
  (hinf : (cluster d (removeSite x ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d n, Connected d (removeSite x ω) a z := by
-- proof
  apply StatMech.Percolation.arc_connected_removeSite_reaches_boundary ω n hn x a hax habox hinf

/--
[arc_neighbour_in_box_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_neighbour_in_box_succ_eq
  {d : ℕ}
  {x c : Site d}
  {n : ℕ}
-- given
  (hx : x ∈ box d n)
  (hadj : (hypercubicLattice d).Adj x c) :
-- imply
  c ∈ box d (n + 1) := by
-- proof
  apply StatMech.Percolation.arc_neighbour_in_box_succ hx hadj

/--
[arc_trif_arm_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_trif_arm_data_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hres : arc_TrifArmsRemoveSiteInfinite ω n)
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x) :
-- imply
  ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d), (∀ i, (openSubgraph d ω).Adj x (c i)) ∧ (∀ i, c i ≠ x) ∧ (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧ ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧ ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧ (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧ ∃ w : (openSubgraph d (removeSite x ω)).Walk (c i) (zr i), x ∉ w.support) := by
-- proof
  apply StatMech.Percolation.arc_trif_arm_data ω n hres x hxbox htri

/--
[arc_armForestReaching_of_residue_single_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_armForestReaching_of_residue_single_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {c : Fin 3 → Site d}
-- given
  (_hxbox : x ∈ box d n)
  (_htri : IsTrifurcation d ω x)
  (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
  (hadj : ∀ i, (openSubgraph d ω).Adj x (c i))
  (hne : ∀ i, c i ≠ x)
  (hcut : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧ ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧ ¬ Connected d (removeSite x ω) (c 1) (c 2))
  (hbdry : ∀ i, c i ∈ vertexBoundary d n)
  (hinj : Function.Injective c) :
-- imply
  sfa_ArmForestReaching ω n := by
-- proof
  apply StatMech.Percolation.arc_armForestReaching_of_residue_single_boundary ω n _hxbox _htri hsingle c hadj hne hcut hbdry hinj

/--
[arc_Tcount_le_boundary_of_residue_single_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_Tcount_le_boundary_of_residue_single_boundary_eq
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
  apply StatMech.Percolation.arc_Tcount_le_boundary_of_residue_single_boundary ω n hxbox htri hsingle c hadj hne hcut hbdry hinj

/--
[arc_p_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_p_adj_eq
  {d : ℕ}
  {k : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (arc_p k) (arc_p (k + 1)) := by
-- proof
  apply StatMech.Percolation.arc_p_adj k

/--
[arc_p_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_p_inj_eq
  {d : ℕ} :
-- imply
  Function.Injective arc_p := by
-- proof
  apply StatMech.Percolation.arc_p_inj

/--
[arc_ray_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_ray_open_eq
  {d : ℕ}
  {k : ℤ}
-- given
  (hk : -1 ≤ k) :
-- imply
  arc_rayConfig s(arc_p k, arc_p (k + 1)) = true := by
-- proof
  apply StatMech.Percolation.arc_ray_open k hk

/--
[arc_ray_edge_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_ray_edge_connected_eq
  {d : ℕ}
  {k : ℤ}
-- given
  (hk : -1 ≤ k) :
-- imply
  Connected 2 arc_rayConfig (arc_p k) (arc_p (k + 1)) := by
-- proof
  apply StatMech.Percolation.arc_ray_edge_connected k hk

/--
[arc_ray_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_ray_connected_eq
  {d : ℕ}
  {m : ℤ}
-- given
  (hm : -1 ≤ m) :
-- imply
  Connected 2 arc_rayConfig (arc_p (-1)) (arc_p m) := by
-- proof
  apply StatMech.Percolation.arc_ray_connected m hm

/--
[arc_p_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_p_outside_box_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  arc_p (n + 1) ∉ box 2 n := by
-- proof
  apply StatMech.Percolation.arc_p_outside_box n

/--
[arc_arm_ambient_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_arm_ambient_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 arc_rayConfig (arc_p (-1))).Infinite := by
-- proof
  apply StatMech.Percolation.arc_arm_ambient_infinite

/--
[arc_armNeighbour_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_armNeighbour_isolated_eq
  {d : ℕ}
  {y : Site 2} :
-- imply
  ¬ (openSubgraph 2 (removeSite (arc_p 0) arc_rayConfig)).Adj (arc_p (-1)) y := by
-- proof
  apply StatMech.Percolation.arc_armNeighbour_isolated y

/--
[arc_arm_removeSite_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_arm_removeSite_finite_eq
  {d : ℕ} :
-- imply
  (cluster 2 (removeSite (arc_p 0) arc_rayConfig) (arc_p (-1))).Finite := by
-- proof
  apply StatMech.Percolation.arc_arm_removeSite_finite

/--
[arc_arm_adj_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_arm_adj_x_eq
  {d : ℕ} :
-- imply
  (openSubgraph 2 arc_rayConfig).Adj (arc_p 0) (arc_p (-1)) := by
-- proof
  apply StatMech.Percolation.arc_arm_adj_x

/--
[arc_ambientInfinite_not_removeSiteInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean)
-/
@[path]
private lemma arc_ambientInfinite_not_removeSiteInfinite_eq
  {d : ℕ} :
-- imply
  ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x a : Site 2), (openSubgraph 2 ω).Adj x a ∧ Connected 2 ω x a ∧ (cluster 2 ω a).Infinite ∧ ¬ (cluster 2 (removeSite x ω) a).Infinite := by
-- proof
  apply StatMech.Percolation.arc_ambientInfinite_not_removeSiteInfinite


-- created on 2026-10-23
