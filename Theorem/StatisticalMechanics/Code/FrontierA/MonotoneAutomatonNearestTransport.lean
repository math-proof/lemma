/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonPairLaw.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NearestSetGeometry.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteTargetTransport
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestTransport
open Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem pairLowInfiniteVertices_nonempty (omega : PairSiteConfig d)
    {x : Site d} (hx : (cluster d (siteToBond (pairSiteLeft omega)) x).Infinite) :
    (pairLowInfiniteVertices omega).Nonempty := by
  exact ⟨x, hx⟩


theorem pairHighCluster_nonempty (omega : PairSiteConfig d) (x : Site d) :
    (pairHighCluster omega x).Nonempty :=
  ⟨x, self_mem_cluster _ x⟩


theorem pairNearestHighSet_nonempty (omega : PairSiteConfig d) (x : Site d)
    (hlow : (pairLowInfiniteVertices omega).Nonempty) :
    (pairNearestHighSet omega x).Nonempty :=
  nearestSourceSet_nonempty (pairHighCluster_nonempty omega x) hlow


theorem pairNearestHighFinset_nonempty (omega : PairSiteConfig d) (x : Site d)
    (hlow : (pairLowInfiniteVertices omega).Nonempty)
    (hfin : (pairNearestHighSet omega x).Finite) :
    (pairNearestHighFinset omega x).Nonempty :=
  nearestSourceFinset_nonempty (pairHighCluster_nonempty omega x) hlow hfin


theorem pairNearestHighSet_subset_cluster (omega : PairSiteConfig d) (x : Site d) :
    pairNearestHighSet omega x ⊆ pairHighCluster omega x :=
  nearestSourceSet_subset _ _


theorem pairHighCluster_eq_of_mem {omega : PairSiteConfig d} {x z : Site d}
    (hz : z ∈ pairHighCluster omega x) :
    pairHighCluster omega z = pairHighCluster omega x := by
  exact (cluster_eq_of_connected hz).symm


theorem pairNearestHighSet_eq_of_mem {omega : PairSiteConfig d} {x z : Site d}
    (hz : z ∈ pairHighCluster omega x) :
    pairNearestHighSet omega z = pairNearestHighSet omega x := by
  rw [pairNearestHighSet, pairNearestHighSet, pairHighCluster_eq_of_mem hz]


theorem pairNearestHighFinset_eq_of_mem {omega : PairSiteConfig d} {x z : Site d}
    (hz : z ∈ pairHighCluster omega x) :
    pairNearestHighFinset omega z = pairNearestHighFinset omega x := by
  unfold pairNearestHighFinset
  rw [pairHighCluster_eq_of_mem hz]


end StatMech.FrontierA
