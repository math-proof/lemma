/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ActiveBoundaryDifferential
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Def.StatisticalMechanics.Code.OSSS.WiredBoxDifferential.Part6
open scoped BigOperators Classical
open Finset Set


namespace StatMech

namespace OSSS

namespace WiredBoxDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open ActiveBoundaryDifferential

open FK RevealmentTranslation


theorem wired_box_differential_inequality
    (d n : Nat) (hd : 1 <= d) (hn : 1 <= n)
    (q beta beta0 : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hbeta0 : beta <= beta0) :
    exists c : Real, 0 < c ∧
      c * (Lindeberg.mean
          (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
            (FK.betaParams (fun _ => 1) beta) q)
          (crossIndG (boxActiveEdge d n) 0 n) /
        (4 * (osssBoxFinset d n).sup' (by
            exact ⟨0, origin_mem_osssBoxFinset d n⟩)
          (fun x => ∑ j ∈ Finset.range n,
            Lindeberg.mean
              (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
                (FK.betaParams (fun _ => 1) beta) q)
              (fun omega => if ConnectedToSet d
                (liftCfg (boxActiveEdge d n) omega) x (centeredBoundary x j)
                then (1 : Real) else 0)) / (n : Real))) <=
      deriv (fun b => FK.activeBCProbOf (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams (fun _ => 1) b) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
  letI : Nonempty (boxGraph d n).edgeSet := boxGraph_edgeSet_nonempty d n hd hn
  let Lambda := osssBoxFinset d n
  have hne : Lambda.Nonempty := ⟨0, origin_mem_osssBoxFinset d n⟩
  let disc0 : Nat -> Finset (Site d) := osssBoundaryFinset d
  let C := wiredBoxBoundaryGraph d n
  let J : Sym2 (boxVerts d n) -> Real := fun _ => 1
  have hJ : forall e, 0 < J e := fun _ => by norm_num
  have hinj := boxActiveEdge_injective d n
  have hcoh := boxActiveEdge_eq_endpoints d n
  have hadj := boxActiveEnd_adj d n
  have hl : forall e : (boxGraph d n).edgeSet,
      e ∈ (Finset.univ : Finset (boxGraph d n).edgeSet).toList := by simp
  have hdisc0sub : ∀ k, ∀ x ∈ disc0 k, x ∈ vertexBoundary d k := by
    intro k x hx
    simpa [disc0] using hx
  have hdisc0sup : ∀ k, ∀ x ∈ vertexBoundary d k, x ∈ disc0 k := by
    intro k x hx
    simpa [disc0] using hx
  have hoB : forall k, (0 : Site d) ∉ disc0 k := by
    intro k
    exact origin_not_mem_osssBoundaryFinset d k
  have ho : forall k : Nat, 1 <= k -> (0 : Site d) ∈ box d (k - 1) := by
    intro k hk i
    simp
  have hLu : forall e : (boxGraph d n).edgeSet,
      boxActiveEndU d n e ∈ Lambda := boxActiveEndU_mem d n
  have hLv : forall e : (boxGraph d n).edgeSet,
      boxActiveEndV d n e ∈ Lambda := boxActiveEndV_mem d n
  have hUbox : forall e : (boxGraph d n).edgeSet,
      boxActiveEndU d n e ∈ box d n := fun e => e.1.out.1.property
  have hVbox : forall e : (boxGraph d n).edgeSet,
      boxActiveEndV d n e ∈ box d n := fun e => e.1.out.2.property
  have hmain := activeBC_fk_differential_inequality
    (boxGraph d n) C J hJ q beta beta0 hq hbeta hbeta0 hinj hcoh hadj
    (0 : Site d) (Finset.univ : Finset (boxGraph d n).edgeSet).toList hl
    disc0 hdisc0sub hdisc0sup hoB ho n hn Lambda hne hLu hLv hUbox hVbox
  simpa [C, J, Lambda, disc0] using hmain


theorem wired_box_differential_inequality_full
    (d n : Nat) (hd : 1 <= d) (hn : 1 <= n)
    (q beta beta0 : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hbeta0 : beta <= beta0) :
    exists c : Real, 0 < c ∧
      c * (wiredActiveTheta d n q beta / wiredActiveDenom d n q beta) <=
        deriv (wiredFullCrossMass d n q) beta := by
  obtain ⟨c, hc, hmain⟩ := wired_box_differential_inequality
    d n hd hn q beta beta0 hq hbeta hbeta0
  rw [activeBox_cross_deriv_eq_wiredFull d n q beta hq hbeta] at hmain
  exact ⟨c, hc, by
    simpa [wiredActiveTheta, wiredActiveDenom] using hmain⟩

end WiredBoxDifferential
end OSSS
end StatMech
