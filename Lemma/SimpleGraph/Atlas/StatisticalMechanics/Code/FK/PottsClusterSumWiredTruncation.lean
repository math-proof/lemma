import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncation
open Filter MeasureTheory Set Topology StatMech StatMech.FK


/--
[continuous_wiredTruncationEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma continuous_wiredTruncationEdge_eq
  {d n : Nat} :
-- imply
  Continuous (wiredTruncationEdge d n) := by
-- proof
  apply StatMech.FK.continuous_wiredTruncationEdge d n

/--
[tendsto_wiredTruncationEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma tendsto_wiredTruncationEdge_eq
  {d : Nat}
  {omega : ConfigSpace (Sym2 (Site d))} :
-- imply
  Tendsto (fun n => wiredTruncationEdge d n omega) atTop (nhds omega) := by
-- proof
  apply StatMech.FK.tendsto_wiredTruncationEdge omega

/--
[boxOpen_adj_of_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma boxOpen_adj_of_full_eq
  {d n : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x y : boxVerts d n}
-- given
  (hxy : (openSubgraph d omega).Adj (x : Site d) (y : Site d)) :
-- imply
  (openSub (boxGraph d n) (boxRestrict d n omega)).Adj x y := by
-- proof
  apply StatMech.FK.boxOpen_adj_of_full omega hxy

/--
[connToBdry_boxRestrict_of_connected_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma connToBdry_boxRestrict_of_connected_outside_eq
  {d n : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : boxVerts d n}
  {v : Site d}
-- given
  (hn : 1 <= n)
  (hv : v ∉ box d n)
  (hreach : Lattice.Connected d omega (x : Site d) v) :
-- imply
  IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n omega) x := by
-- proof
  apply StatMech.FK.connToBdry_boxRestrict_of_connected_outside hn omega x hv hreach

/--
[cluster_wiredTruncationEdge_eq_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma cluster_wiredTruncationEdge_eq_of_finite_eq
  {d n : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hd : 2 <= d)
  (hn : 1 <= n)
  (hx : x ∈ box d n)
  (hfinite : (cluster d (wiredTruncationEdge d n omega) x).Finite) :
-- imply
  cluster d (wiredTruncationEdge d n omega) x = cluster d omega x := by
-- proof
  apply StatMech.FK.cluster_wiredTruncationEdge_eq_of_finite hd hn omega x hx hfinite

/--
[cluster_wiredTruncationEdge_infinite_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma cluster_wiredTruncationEdge_infinite_of_infinite_eq
  {d n : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hd : 2 <= d)
  (hn : 1 <= n)
  (hx : x ∈ box d n)
  (hinfinite : (cluster d omega x).Infinite) :
-- imply
  (cluster d (wiredTruncationEdge d n omega) x).Infinite := by
-- proof
  apply StatMech.FK.cluster_wiredTruncationEdge_infinite_of_infinite hd hn omega x hx hinfinite

/--
[eventually_cluster_wiredTruncationEdge_eq_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma eventually_cluster_wiredTruncationEdge_eq_of_finite_eq
  {d : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hfinite : (cluster d omega x).Finite) :
-- imply
  ∀ᶠ n in atTop, cluster d (wiredTruncationEdge d n omega) x = cluster d omega x := by
-- proof
  apply StatMech.FK.eventually_cluster_wiredTruncationEdge_eq_of_finite omega x hfinite

/--
[pottsClusterSumSpin_wiredTruncationEdge_eq_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma pottsClusterSumSpin_wiredTruncationEdge_eq_of_finite_eq
  {d q n : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hd : 2 <= d)
  (hn : 1 <= n)
  (label : Site d -> Fin q)
  (hx : x ∈ box d n)
  (hfinite : (cluster d (wiredTruncationEdge d n omega) x).Finite) :
-- imply
  pottsClusterSumSpin boundaryColor (wiredTruncationEdge d n omega) label x = pottsClusterSumSpin boundaryColor omega label x := by
-- proof
  apply StatMech.FK.pottsClusterSumSpin_wiredTruncationEdge_eq_of_finite hd hn boundaryColor omega label x hx hfinite

/--
[cluster_status_of_pottsClusterSumSpin_wiredTruncationEdge_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma cluster_status_of_pottsClusterSumSpin_wiredTruncationEdge_ne_eq
  {d q n : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hd : 2 <= d)
  (hn : 1 <= n)
  (label : Site d -> Fin q)
  (hx : x ∈ box d n)
  (hne : pottsClusterSumSpin boundaryColor (wiredTruncationEdge d n omega) label x ≠ pottsClusterSumSpin boundaryColor omega label x) :
-- imply
  (cluster d (wiredTruncationEdge d n omega) x).Infinite ∧ (cluster d omega x).Finite := by
-- proof
  apply StatMech.FK.cluster_status_of_pottsClusterSumSpin_wiredTruncationEdge_ne hd hn boundaryColor omega label x hx hne

/--
[eventually_cluster_wiredTruncationEdge_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma eventually_cluster_wiredTruncationEdge_infinite_eq
  {d : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hd : 2 <= d)
  (hinfinite : (cluster d omega x).Infinite) :
-- imply
  ∀ᶠ n in atTop, (cluster d (wiredTruncationEdge d n omega) x).Infinite := by
-- proof
  apply StatMech.FK.eventually_cluster_wiredTruncationEdge_infinite hd omega x hinfinite

/--
[eventually_pottsClusterSumSpin_wiredTruncationEdge_eq_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma eventually_pottsClusterSumSpin_wiredTruncationEdge_eq_of_finite_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (label : Site d -> Fin q)
  (hfinite : (cluster d omega x).Finite) :
-- imply
  ∀ᶠ n in atTop, pottsClusterSumSpin boundaryColor (wiredTruncationEdge d n omega) label x = pottsClusterSumSpin boundaryColor omega label x := by
-- proof
  apply StatMech.FK.eventually_pottsClusterSumSpin_wiredTruncationEdge_eq_of_finite boundaryColor omega label x hfinite

/--
[eventually_pottsClusterSumSpin_wiredTruncationEdge_eq_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma eventually_pottsClusterSumSpin_wiredTruncationEdge_eq_of_infinite_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hd : 2 <= d)
  (label : Site d -> Fin q)
  (hinfinite : (cluster d omega x).Infinite) :
-- imply
  ∀ᶠ n in atTop, pottsClusterSumSpin boundaryColor (wiredTruncationEdge d n omega) label x = pottsClusterSumSpin boundaryColor omega label x := by
-- proof
  apply StatMech.FK.eventually_pottsClusterSumSpin_wiredTruncationEdge_eq_of_infinite hd boundaryColor omega label x hinfinite

/--
[eventually_pottsClusterSumSpin_wiredTruncationEdge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncation.lean)
-/
@[path]
private lemma eventually_pottsClusterSumSpin_wiredTruncationEdge_eq_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hd : 2 <= d)
  (label : Site d -> Fin q) :
-- imply
  ∀ᶠ n in atTop, pottsClusterSumSpin boundaryColor (wiredTruncationEdge d n omega) label x = pottsClusterSumSpin boundaryColor omega label x := by
-- proof
  apply StatMech.FK.eventually_pottsClusterSumSpin_wiredTruncationEdge_eq hd boundaryColor omega label x


-- created on 2026-10-23
