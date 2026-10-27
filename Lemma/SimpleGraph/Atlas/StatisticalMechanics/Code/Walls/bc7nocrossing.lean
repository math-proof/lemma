import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc7nocrossing
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc7_cut_connected_of_openEdge_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7nocrossing.lean)
-/
@[path]
private lemma bc7_cut_connected_of_openEdge_between_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y u v : Site d}
-- given
  (hxu : Connected d (removeSite 0 ω) x u)
  (hvy : Connected d (removeSite 0 ω) y v)
  (huv : IsOpenEdge d (removeSite 0 ω) u v) :
-- imply
  Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Walls.bc7_cut_connected_of_openEdge_between hxu hvy huv

/--
[bc7_cut_clusters_eq_of_openEdge_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7nocrossing.lean)
-/
@[path]
private lemma bc7_cut_clusters_eq_of_openEdge_between_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y u v : Site d}
-- given
  (hxu : Connected d (removeSite 0 ω) x u)
  (hvy : Connected d (removeSite 0 ω) y v)
  (huv : IsOpenEdge d (removeSite 0 ω) u v) :
-- imply
  cluster d (removeSite 0 ω) x = cluster d (removeSite 0 ω) y := by
-- proof
  apply StatMech.Walls.bc7_cut_clusters_eq_of_openEdge_between hxu hvy huv

/--
[bc7_cut_no_crossing_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7nocrossing.lean)
-/
@[path]
private lemma bc7_cut_no_crossing_pair_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y u v : Site d}
-- given
  (hu : u ∈ cluster d (removeSite 0 ω) x)
  (hv : v ∈ cluster d (removeSite 0 ω) y)
  (huv : IsOpenEdge d (removeSite 0 ω) u v) :
-- imply
  cluster d (removeSite 0 ω) x = cluster d (removeSite 0 ω) y := by
-- proof
  apply StatMech.Walls.bc7_cut_no_crossing_pair hu hv huv

/--
[bc7_cut_no_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7nocrossing.lean)
-/
@[path]
private lemma bc7_cut_no_crossing_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hne : cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y) :
-- imply
  ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x → ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y → ¬ IsOpenEdge d (removeSite 0 ω) u v := by
-- proof
  apply StatMech.Walls.bc7_cut_no_crossing hne

/--
[bc7_cut_no_crossing_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7nocrossing.lean)
-/
@[path]
private lemma bc7_cut_no_crossing_set_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y u v : Site d}
-- given
  (hne : cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y)
  (hu : u ∈ cluster d (removeSite 0 ω) x)
  (huv : IsOpenEdge d (removeSite 0 ω) u v) :
-- imply
  v ∉ cluster d (removeSite 0 ω) y := by
-- proof
  apply StatMech.Walls.bc7_cut_no_crossing_set hne hu huv

/--
[bc7_cut_edge_stays_in_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7nocrossing.lean)
-/
@[path]
private lemma bc7_cut_edge_stays_in_cluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x u v : Site d}
-- given
  (hu : u ∈ cluster d (removeSite 0 ω) x)
  (huv : IsOpenEdge d (removeSite 0 ω) u v) :
-- imply
  v ∈ cluster d (removeSite 0 ω) x := by
-- proof
  apply StatMech.Walls.bc7_cut_edge_stays_in_cluster hu huv

/--
[bc7_offBoxCluster_mem_cutCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7nocrossing.lean)
-/
@[path]
private lemma bc7_offBoxCluster_mem_cutCluster_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hx : x ∈ bc6_offBoxCluster N a R ω) :
-- imply
  x ∈ cluster d (removeSite 0 ω) (hrHD_rayPt a (R : ℤ)) := by
-- proof
  apply StatMech.Walls.bc7_offBoxCluster_mem_cutCluster hx

/--
[bc7_offBoxCluster_no_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7nocrossing.lean)
-/
@[path]
private lemma bc7_offBoxCluster_no_crossing_eq
  {d : ℕ}
  {N : ℕ}
  {a c : Fin d}
  {Ra Rc : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hne : cluster d (removeSite 0 ω) (hrHD_rayPt a (Ra : ℤ)) ≠ cluster d (removeSite 0 ω) (hrHD_rayPt c (Rc : ℤ)))
  (hu : u ∈ bc6_offBoxCluster N a Ra ω)
  (hv : v ∈ bc6_offBoxCluster N c Rc ω) :
-- imply
  ¬ IsOpenEdge d (removeSite 0 ω) u v := by
-- proof
  apply StatMech.Walls.bc7_offBoxCluster_no_crossing hne hu hv


-- created on 2026-10-23
