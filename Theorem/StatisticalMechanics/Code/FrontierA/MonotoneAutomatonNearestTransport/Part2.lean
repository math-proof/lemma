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
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestTransport.Part2
open Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem pairNearestTransport_outgoing_le_one (omega : PairSiteConfig d)
    (x : Site d) :
    ∑' y : Site d, pairNearestTransport x y omega ≤ 1 :=
  finiteTargetTransport_outgoing_le_one
    (pairHighCluster omega x) (pairNearestHighFinset omega x) x


theorem zero_not_mem_pairNearestHighFinset_of_not_cluster
    (omega : PairSiteConfig d) {x : Site d}
    (hx : x ∉ pairHighCluster omega 0) :
    (0 : Site d) ∉ pairNearestHighFinset omega x := by
  intro hzero
  have hzeroSet := mem_nearestSourceSet_of_mem_finset hzero
  have hzeroCluster : (0 : Site d) ∈ pairHighCluster omega x :=
    pairNearestHighSet_subset_cluster omega x hzeroSet
  have hx0 : Connected d (siteToBond (pairSiteRight omega)) x 0 := hzeroCluster
  exact hx hx0.symm


theorem pairNearestTransport_to_zero_eq_fixed (omega : PairSiteConfig d) :
    (fun x => pairNearestTransport x 0 omega) =
      fun x => finiteTargetTransport (pairHighCluster omega 0)
        (pairNearestHighFinset omega 0) x 0 := by
  funext x
  by_cases hx : x ∈ pairHighCluster omega 0
  · unfold pairNearestTransport
    rw [pairHighCluster_eq_of_mem hx, pairNearestHighFinset_eq_of_mem hx]
  · have hzero : (0 : Site d) ∉ pairNearestHighFinset omega x :=
      zero_not_mem_pairNearestHighFinset_of_not_cluster omega hx
    rw [finiteTargetTransport_outside _ _ hx]
    simp [pairNearestTransport, finiteTargetTransport, hzero]


theorem pairNearestTransport_incoming_eq_top
    (omega : PairSiteConfig d)
    (hhigh : (pairHighCluster omega 0).Infinite)
    (hlow : (pairLowInfiniteVertices omega).Nonempty)
    (hfin : (pairNearestHighSet omega 0).Finite)
    (hzero : (0 : Site d) ∈ pairNearestHighSet omega 0) :
    ∑' x : Site d, pairNearestTransport x 0 omega = ⊤ := by
  rw [pairNearestTransport_to_zero_eq_fixed]
  exact finiteTargetTransport_incoming_eq_top
    (pairHighCluster omega 0) (pairNearestHighFinset omega 0) hhigh
    (pairNearestHighFinset_nonempty omega 0 hlow hfin)
    ((mem_nearestSourceFinset_iff hfin 0).2 hzero)


theorem pairSiteLeft_shift (g : Multiplicative (Site d))
    (omega : PairSiteConfig d) :
    pairSiteLeft (StatMech.ConfigSpace.shift g omega) =
      StatMech.ConfigSpace.shift g (pairSiteLeft omega) := by
  funext x
  rfl

theorem pairSiteRight_shift (g : Multiplicative (Site d))
    (omega : PairSiteConfig d) :
    pairSiteRight (StatMech.ConfigSpace.shift g omega) =
      StatMech.ConfigSpace.shift g (pairSiteRight omega) := by
  funext x
  rfl


theorem siteCluster_factor_shift (g : Multiplicative (Site d))
    (eta : ConfigSpace (Site d)) (x : Site d) :
    cluster d (siteToBond (StatMech.ConfigSpace.shift g eta)) (g • x) =
      translateSiteSet (Multiplicative.toAdd g)
        (cluster d (siteToBond eta) x) := by
  rw [siteToBond_shift, cluster_shift]
  rfl


theorem pairHighCluster_shift (g : Multiplicative (Site d))
    (omega : PairSiteConfig d) (x : Site d) :
    pairHighCluster (StatMech.ConfigSpace.shift g omega) (g • x) =
      translateSiteSet (Multiplicative.toAdd g) (pairHighCluster omega x) := by
  unfold pairHighCluster
  rw [pairSiteRight_shift, siteCluster_factor_shift]


theorem pairLowInfiniteVertices_shift (g : Multiplicative (Site d))
    (omega : PairSiteConfig d) :
    pairLowInfiniteVertices (StatMech.ConfigSpace.shift g omega) =
      translateSiteSet (Multiplicative.toAdd g)
        (pairLowInfiniteVertices omega) := by
  ext z
  let x : Site d := g⁻¹ • z
  have hzx : g • x = z := by simp [x]
  constructor
  · intro hz
    have hz' : (cluster d
        (siteToBond (pairSiteLeft (StatMech.ConfigSpace.shift g omega)))
        (g • x)).Infinite := by simpa [hzx] using hz
    rw [pairSiteLeft_shift, siteCluster_factor_shift] at hz'
    have hxinf : (cluster d (siteToBond (pairSiteLeft omega)) x).Infinite := by
      exact (Set.infinite_image_iff
        (Set.injOn_of_injective (smul_injective g))).mp hz'
    exact ⟨x, hxinf, hzx⟩
  · rintro ⟨y, hy, rfl⟩
    have hyinf : (cluster d (siteToBond (pairSiteLeft omega)) y).Infinite := hy
    have himg : (translateSiteSet (Multiplicative.toAdd g)
        (cluster d (siteToBond (pairSiteLeft omega)) y)).Infinite := by
      exact Set.Infinite.image (smul_injective g).injOn hyinf
    rw [← siteCluster_factor_shift, ← pairSiteLeft_shift] at himg
    exact himg


theorem pairNearestHighSet_shift (g : Multiplicative (Site d))
    (omega : PairSiteConfig d) (x : Site d) :
    pairNearestHighSet (StatMech.ConfigSpace.shift g omega) (g • x) =
      translateSiteSet (Multiplicative.toAdd g) (pairNearestHighSet omega x) := by
  unfold pairNearestHighSet
  rw [pairHighCluster_shift, pairLowInfiniteVertices_shift,
    nearestSourceSet_translate]


theorem pairNearestHighFinset_shift (g : Multiplicative (Site d))
    (omega : PairSiteConfig d) (x : Site d) :
    pairNearestHighFinset (StatMech.ConfigSpace.shift g omega) (g • x) =
      (pairNearestHighFinset omega x).image (fun z => g • z) := by
  unfold pairNearestHighFinset
  rw [pairHighCluster_shift, pairLowInfiniteVertices_shift,
    nearestSourceFinset_translate]
  rfl


theorem pairNearestTransport_diagonallyInvariant :
    IsDiagonallyInvariantTransport
      (pairNearestTransport (d := d)) := by
  intro g x y omega
  unfold pairNearestTransport
  rw [pairHighCluster_shift, pairNearestHighFinset_shift]
  exact finiteTargetTransport_image (fun z : Site d => g • z)
    (smul_injective g) (pairHighCluster omega x)
    (pairNearestHighFinset omega x) x y

end StatMech.FrontierA
