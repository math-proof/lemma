import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestTransport.Part2
open Set StatMech StatMech.FrontierA


/--
[pairLowInfiniteVertices_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairLowInfiniteVertices_nonempty_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
  {x : Site d}
-- given
  (hx : (cluster d (siteToBond (pairSiteLeft omega)) x).Infinite) :
-- imply
  (pairLowInfiniteVertices omega).Nonempty := by
-- proof
  apply StatMech.FrontierA.pairLowInfiniteVertices_nonempty omega hx

/--
[pairHighCluster_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairHighCluster_nonempty_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
  {x : Site d} :
-- imply
  (pairHighCluster omega x).Nonempty := by
-- proof
  apply StatMech.FrontierA.pairHighCluster_nonempty omega x

/--
[pairNearestHighSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairNearestHighSet_nonempty_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
  {x : Site d}
-- given
  (hlow : (pairLowInfiniteVertices omega).Nonempty) :
-- imply
  (pairNearestHighSet omega x).Nonempty := by
-- proof
  apply StatMech.FrontierA.pairNearestHighSet_nonempty omega x hlow

/--
[pairNearestHighFinset_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairNearestHighFinset_nonempty_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
  {x : Site d}
-- given
  (hlow : (pairLowInfiniteVertices omega).Nonempty)
  (hfin : (pairNearestHighSet omega x).Finite) :
-- imply
  (pairNearestHighFinset omega x).Nonempty := by
-- proof
  apply StatMech.FrontierA.pairNearestHighFinset_nonempty omega x hlow hfin

/--
[pairNearestHighSet_subset_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairNearestHighSet_subset_cluster_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
  {x : Site d} :
-- imply
  pairNearestHighSet omega x ⊆ pairHighCluster omega x := by
-- proof
  apply StatMech.FrontierA.pairNearestHighSet_subset_cluster omega x

/--
[pairHighCluster_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairHighCluster_eq_of_mem_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
  {x z : Site d}
-- given
  (hz : z ∈ pairHighCluster omega x) :
-- imply
  pairHighCluster omega z = pairHighCluster omega x := by
-- proof
  apply StatMech.FrontierA.pairHighCluster_eq_of_mem hz

/--
[pairNearestHighSet_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairNearestHighSet_eq_of_mem_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
  {x z : Site d}
-- given
  (hz : z ∈ pairHighCluster omega x) :
-- imply
  pairNearestHighSet omega z = pairNearestHighSet omega x := by
-- proof
  apply StatMech.FrontierA.pairNearestHighSet_eq_of_mem hz

/--
[pairNearestHighFinset_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairNearestHighFinset_eq_of_mem_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
  {x z : Site d}
-- given
  (hz : z ∈ pairHighCluster omega x) :
-- imply
  pairNearestHighFinset omega z = pairNearestHighFinset omega x := by
-- proof
  apply StatMech.FrontierA.pairNearestHighFinset_eq_of_mem hz

/--
[pairNearestTransport_outgoing_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairNearestTransport_outgoing_le_one_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
  {x : Site d} :
-- imply
  ∑' y : Site d, pairNearestTransport x y omega ≤ 1 := by
-- proof
  apply StatMech.FrontierA.pairNearestTransport_outgoing_le_one omega x

/--
[zero_not_mem_pairNearestHighFinset_of_not_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma zero_not_mem_pairNearestHighFinset_of_not_cluster_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
  {x : Site d}
-- given
  (hx : x ∉ pairHighCluster omega 0) :
-- imply
  (0 : Site d) ∉ pairNearestHighFinset omega x := by
-- proof
  apply StatMech.FrontierA.zero_not_mem_pairNearestHighFinset_of_not_cluster omega hx

/--
[pairNearestTransport_to_zero_eq_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairNearestTransport_to_zero_eq_fixed_eq
  {d : ℕ}
  {omega : PairSiteConfig d} :
-- imply
  (fun x => pairNearestTransport x 0 omega) = fun x => finiteTargetTransport (pairHighCluster omega 0) (pairNearestHighFinset omega 0) x 0 := by
-- proof
  apply StatMech.FrontierA.pairNearestTransport_to_zero_eq_fixed omega

/--
[pairNearestTransport_incoming_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairNearestTransport_incoming_eq_top_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
-- given
  (hhigh : (pairHighCluster omega 0).Infinite)
  (hlow : (pairLowInfiniteVertices omega).Nonempty)
  (hfin : (pairNearestHighSet omega 0).Finite)
  (hzero : (0 : Site d) ∈ pairNearestHighSet omega 0) :
-- imply
  ∑' x : Site d, pairNearestTransport x 0 omega = ⊤ := by
-- proof
  apply StatMech.FrontierA.pairNearestTransport_incoming_eq_top omega hhigh hlow hfin hzero

/--
[pairSiteLeft_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairSiteLeft_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {omega : PairSiteConfig d} :
-- imply
  pairSiteLeft (StatMech.ConfigSpace.shift g omega) = StatMech.ConfigSpace.shift g (pairSiteLeft omega) := by
-- proof
  apply StatMech.FrontierA.pairSiteLeft_shift g omega

/--
[pairSiteRight_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairSiteRight_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {omega : PairSiteConfig d} :
-- imply
  pairSiteRight (StatMech.ConfigSpace.shift g omega) = StatMech.ConfigSpace.shift g (pairSiteRight omega) := by
-- proof
  apply StatMech.FrontierA.pairSiteRight_shift g omega

/--
[siteCluster_factor_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma siteCluster_factor_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {eta : ConfigSpace (Site d)}
  {x : Site d} :
-- imply
  cluster d (siteToBond (StatMech.ConfigSpace.shift g eta)) (g • x) = translateSiteSet (Multiplicative.toAdd g) (cluster d (siteToBond eta) x) := by
-- proof
  apply StatMech.FrontierA.siteCluster_factor_shift g eta x

/--
[pairHighCluster_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairHighCluster_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {omega : PairSiteConfig d}
  {x : Site d} :
-- imply
  pairHighCluster (StatMech.ConfigSpace.shift g omega) (g • x) = translateSiteSet (Multiplicative.toAdd g) (pairHighCluster omega x) := by
-- proof
  apply StatMech.FrontierA.pairHighCluster_shift g omega x

/--
[pairLowInfiniteVertices_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairLowInfiniteVertices_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {omega : PairSiteConfig d} :
-- imply
  pairLowInfiniteVertices (StatMech.ConfigSpace.shift g omega) = translateSiteSet (Multiplicative.toAdd g) (pairLowInfiniteVertices omega) := by
-- proof
  apply StatMech.FrontierA.pairLowInfiniteVertices_shift g omega

/--
[pairNearestHighSet_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairNearestHighSet_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {omega : PairSiteConfig d}
  {x : Site d} :
-- imply
  pairNearestHighSet (StatMech.ConfigSpace.shift g omega) (g • x) = translateSiteSet (Multiplicative.toAdd g) (pairNearestHighSet omega x) := by
-- proof
  apply StatMech.FrontierA.pairNearestHighSet_shift g omega x

/--
[pairNearestHighFinset_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairNearestHighFinset_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {omega : PairSiteConfig d}
  {x : Site d} :
-- imply
  pairNearestHighFinset (StatMech.ConfigSpace.shift g omega) (g • x) = (pairNearestHighFinset omega x).image (fun z => g • z) := by
-- proof
  apply StatMech.FrontierA.pairNearestHighFinset_shift g omega x

/--
[pairNearestTransport_diagonallyInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean)
-/
@[path]
private lemma pairNearestTransport_diagonallyInvariant_eq
  {d : ℕ} :
-- imply
  IsDiagonallyInvariantTransport (pairNearestTransport (d := d)) := by
-- proof
  apply StatMech.FrontierA.pairNearestTransport_diagonallyInvariant


-- created on 2026-10-23
