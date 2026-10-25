/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.CenteredFirstHit
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxLocalized.Part3
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Def.StatisticalMechanics.Code.OSSS.WiredBoxOffCentre.Part2
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxOffCentre

open Lattice IsingFK RevealmentConstruction TreeComplete RevealmentTranslation CenteredFirstHit

open FK

open WiredBoxLocalized

theorem transShellEvent_increasing (d k : Nat) (x : Site d) :
    IsIncreasing (transShellEvent d k x) := by
  intro rho eta hle hrho
  obtain ⟨y, hy, hreach⟩ := hrho
  exact ⟨y, hy, hreach.mono (openSub_mono _ hle)⟩

theorem centeredShellEvent_increasing (d k : Nat) :
    IsIncreasing (centeredShellEvent d k) := by
  intro rho eta hle hrho
  obtain ⟨y, hy, hreach⟩ := hrho
  exact ⟨y, hy, hreach.mono (openSub_mono _ hle)⟩


theorem centeredShellEvent_eq_connToBdryEventLE (d k : Nat) (hk1 : 1 <= k) :
    centeredShellEvent d k = connToBdryEventLE d (n_le_two_mul k) := by
  ext rho
  let omega : ConfigSpace (Sym2 (Site d)) := extendEdge d (2 * k) rho
  have houter : boxRestrict d (2 * k) omega = rho := by
    simp [omega, boxRestrict_extendEdge]
  have hinner : boxRestrict d k omega =
      boxRestrictLE d (n_le_two_mul k) rho := by
    rw [← boxRestrictLE_boxRestrict d (n_le_two_mul k) omega, houter]
  constructor
  · rintro ⟨y, hy, hreach⟩
    have hamb : Connected d omega 0 (y : Site d) := by
      have hc := connected_of_boxConnected (2 * k) omega
        (by simpa [houter] using hreach)
      simpa [IsingFK.boxOrigin, Percolation.origin] using hc
    have hyCentered : (y : Site d) ∈ centeredBoundary 0 k := by
      change centeredRadius 0 (y : Site d) = k
      rw [centeredRadius_zero]
      exact hy
    obtain ⟨z, hz, hwithin⟩ :=
      connected_centeredBoundary_has_within hyCentered hamb
    let hom := zeroWithinToBoxHom d k k le_rfl omega
    have hreachBox := hwithin.map hom
    have hzBdry : boxBoundary d k (hom z) := by
      rw [boxBoundary, mem_vertexBoundary]
      constructor
      · exact (hom z).2
      · intro hsmall
        have hradle : siteRadius (z : Site d) <= k - 1 :=
          mem_box_iff_siteRadius_le.mp hsmall
        change centeredRadius 0 (z : Site d) = k at hz
        rw [centeredRadius_zero] at hz
        omega
    refine ⟨hom z, hzBdry, ?_⟩
    simpa [hinner, hom] using hreachBox
  · rintro ⟨y, hy, hreach⟩
    have hreach' :
        (openSub (boxGraph d k) (boxRestrict d k omega)).Reachable
          (IsingFK.boxOrigin d k) y := by
      simpa [hinner] using hreach
    have hamb : Connected d omega 0 (y : Site d) := by
      simpa [IsingFK.boxOrigin, Percolation.origin] using
        connected_of_boxConnected k omega hreach'
    have hyCentered : (y : Site d) ∈ centeredBoundary 0 k := by
      rw [boxBoundary, mem_vertexBoundary] at hy
      change centeredRadius 0 (y : Site d) = k
      rw [centeredRadius_zero]
      exact siteRadius_eq_of_mem_vertexBoundary hy
    obtain ⟨z, hz, hwithin⟩ :=
      connected_centeredBoundary_has_within hyCentered hamb
    let hom := zeroWithinToBoxHom d k (2 * k) (n_le_two_mul k) omega
    have hreachOuter := hwithin.map hom
    refine ⟨hom z, ?_, ?_⟩
    · change siteRadius (z : Site d) = k
      change centeredRadius 0 (z : Site d) = k at hz
      rwa [centeredRadius_zero] at hz
    · simpa [houter, hom] using hreachOuter


theorem openSub_boxRestrict_liftActive_eq (d R : Nat)
    (rho : ConfigSpace (Sym2 (boxVerts d R))) :
    openSub (boxGraph d R)
        (boxRestrict d R
          (liftCfg (WiredBoxDifferential.boxActiveEdge d R)
            (restrictActive (boxGraph d R) rho))) =
      openSub (boxGraph d R) rho := by
  ext u v
  simp only [openSub_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    let e : (boxGraph d R).edgeSet :=
      ⟨s(u, v), by rw [SimpleGraph.mem_edgeSet]; exact hadj⟩
    have hlift := liftCfg_apply_edge
      (WiredBoxDifferential.boxActiveEdge_injective d R)
      (restrictActive (boxGraph d R) rho) e
    change liftCfg (WiredBoxDifferential.boxActiveEdge d R)
      (restrictActive (boxGraph d R) rho)
        (edgeIncl d R s(u, v)) = true at hopen
    have hedge : WiredBoxDifferential.boxActiveEdge d R e =
        edgeIncl d R s(u, v) := rfl
    rw [← hedge, hlift] at hopen
    exact hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    let e : (boxGraph d R).edgeSet :=
      ⟨s(u, v), by rw [SimpleGraph.mem_edgeSet]; exact hadj⟩
    have hlift := liftCfg_apply_edge
      (WiredBoxDifferential.boxActiveEdge_injective d R)
      (restrictActive (boxGraph d R) rho) e
    change liftCfg (WiredBoxDifferential.boxActiveEdge d R)
      (restrictActive (boxGraph d R) rho)
        (edgeIncl d R s(u, v)) = true
    have hedge : WiredBoxDifferential.boxActiveEdge d R e =
        edgeIncl d R s(u, v) := rfl
    rw [← hedge, hlift]
    exact hopen


theorem activeCrossInd_eq_connToBdry_indicator
    (d R : Nat) (hR : 1 <= R)
    (rho : ConfigSpace (Sym2 (boxVerts d R))) :
    AdaptiveCovLowerGeom.crossIndG
        (WiredBoxDifferential.boxActiveEdge d R) 0 R
        (restrictActive (boxGraph d R) rho) =
      ({eta : ConfigSpace (Sym2 (boxVerts d R)) |
        ConnToBdry (boxGraph d R) (boxBoundary d R) eta
          (IsingFK.boxOrigin d R)}).indicator (fun _ => (1 : Real)) rho := by
  let omega : ConfigSpace (Sym2 (Site d)) :=
    liftCfg (WiredBoxDifferential.boxActiveEdge d R)
      (restrictActive (boxGraph d R) rho)
  have hopenEq := openSub_boxRestrict_liftActive_eq d R rho
  have hevent :
      ConnectedToSet d omega 0 (vertexBoundary d R) ↔
      ConnToBdry (boxGraph d R) (boxBoundary d R) rho
        (IsingFK.boxOrigin d R) := by
    constructor
    · intro hconn
      obtain ⟨y, hy, hxy⟩ := hconn
      obtain ⟨z, hz, hwithin⟩ :=
        connected_centeredBoundary_has_within
          (show y ∈ centeredBoundary 0 R by
            change centeredRadius 0 y = R
            rw [centeredRadius_zero]
            exact siteRadius_eq_of_mem_vertexBoundary hy)
          hxy
      let hom := zeroWithinToBoxHom d R R le_rfl omega
      have hreach := hwithin.map hom
      have hzBdry : boxBoundary d R (hom z) := by
        rw [boxBoundary, mem_vertexBoundary]
        constructor
        · exact (hom z).2
        · intro hsmall
          have hradle := mem_box_iff_siteRadius_le.mp hsmall
          rw [zeroWithinToBoxHom_val] at hradle
          change centeredRadius 0 (z : Site d) = R at hz
          rw [centeredRadius_zero] at hz
          omega
      refine ⟨hom z, hzBdry, ?_⟩
      change (openSub (boxGraph d R) rho).Reachable
        (IsingFK.boxOrigin d R) (hom z)
      rw [← hopenEq]
      simpa [hom, omega] using hreach
    · rintro ⟨y, hy, hreach⟩
      have hreach' :
          (openSub (boxGraph d R) (boxRestrict d R omega)).Reachable
            (IsingFK.boxOrigin d R) y := by
        rw [hopenEq]
        exact hreach
      have hamb := connected_of_boxConnected R omega hreach'
      refine ⟨(y : Site d), ?_, ?_⟩
      · simpa [boxBoundary] using hy
      · simpa [IsingFK.boxOrigin, Percolation.origin, omega] using hamb
  unfold AdaptiveCovLowerGeom.crossIndG
  rw [Set.indicator_apply, Set.indicator_apply]
  change (if ConnectedToSet d omega 0 (vertexBoundary d R) then 1 else 0) =
    (if ConnToBdry (boxGraph d R) (boxBoundary d R) rho
      (IsingFK.boxOrigin d R) then 1 else 0)
  by_cases h : ConnectedToSet d omega 0 (vertexBoundary d R)
  · rw [if_pos h, if_pos (hevent.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (hevent.mpr hc))]


theorem restrictActive_boxRestrictLE (d : Nat) {r R : Nat} (hrR : r <= R)
    (rho : ConfigSpace (Sym2 (boxVerts d R))) :
    restrictConfig (WiredBoxLocalized.boxActiveEdgeLE d hrR)
        (restrictActive (boxGraph d R) rho) =
      restrictActive (boxGraph d r) (boxRestrictLE d hrR rho) := by
  funext e
  rfl

theorem innerCrossInd_restrictActive_eq_centeredShell_indicator
    (d k : Nat) (hk1 : 1 <= k)
    (rho : ConfigSpace (Sym2 (boxVerts d (2 * k)))) :
    WiredBoxLocalized.innerCrossInd d k
        (restrictActive (boxGraph d (2 * k)) rho) =
      (centeredShellEvent d k).indicator (fun _ => (1 : Real)) rho := by
  unfold WiredBoxLocalized.innerCrossInd
  rw [restrictActive_boxRestrictLE d (WiredBoxLocalized.n_le_two_mul k) rho]
  rw [activeCrossInd_eq_connToBdry_indicator d k hk1
    (boxRestrictLE d (WiredBoxLocalized.n_le_two_mul k) rho)]
  rw [centeredShellEvent_eq_connToBdryEventLE d k hk1]
  rfl


theorem wiredOuterInnerTheta_eq_centeredShellMass
    (d k : Nat) (hk1 : 1 <= k) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    WiredBoxLocalized.wiredOuterInnerTheta d q beta k =
      ∑ rho,
        (centeredShellEvent d k).indicator (fun _ => (1 : Real)) rho *
          wiredFkProb (boxGraph d (2 * k)) (boxBoundary d (2 * k))
            (1 - Real.exp (-beta)) q rho := by
  have hk0 : k ≠ 0 := by omega
  rw [WiredBoxLocalized.wiredOuterInnerTheta, if_neg hk0]
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
    linarith
  have hp1 : p < 1 := by
    unfold p
    linarith [Real.exp_pos (-beta)]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hparam : FK.betaParams
      (fun _ : Sym2 (boxVerts d (2 * k)) => (1 : Real)) beta = fun _ => p := by
    funext e
    simp [FK.betaParams, p]
  rw [hparam]
  have hmean := activeBCMean_boundaryClique_eq_wired
    (boxGraph d (2 * k)) (boxBoundary d (2 * k)) hp hp1 hq0
    (WiredBoxLocalized.innerCrossInd d k)
  change FK.activeBCMean (boxGraph d (2 * k))
      (Lattice.boundaryCliqueGraph (boxBoundary d (2 * k))) (fun _ => p) q
      (WiredBoxLocalized.innerCrossInd d k) = _
  rw [hmean]
  apply Finset.sum_congr rfl
  intro rho _
  rw [innerCrossInd_restrictActive_eq_centeredShell_indicator d k hk1 rho]

theorem boxActiveEdgeLE_ambient (d : Nat) {r R : Nat} (hrR : r <= R)
    (e : (boxGraph d r).edgeSet) :
    WiredBoxDifferential.boxActiveEdge d R
        (WiredBoxLocalized.boxActiveEdgeLE d hrR e) =
      WiredBoxDifferential.boxActiveEdge d r e := by
  exact edgeIncl_innerEdgeLE d hrR e.1


theorem openSubgraph_liftInner_le_extendOuter
    (d : Nat) {r R : Nat} (hrR : r <= R)
    (rho : ConfigSpace (Sym2 (boxVerts d R))) :
    openSubgraph d
        (liftCfg (WiredBoxDifferential.boxActiveEdge d r)
          (restrictConfig (WiredBoxLocalized.boxActiveEdgeLE d hrR)
            (restrictActive (boxGraph d R) rho))) <=
      openSubgraph d (extendEdge d R rho) := by
  intro y z hyz
  rw [openSubgraph_adj] at hyz ⊢
  refine ⟨hyz.1, ?_⟩
  obtain ⟨e, he, hpair⟩ := exists_abstract_open_edge
    (WiredBoxDifferential.boxActiveEdge_eq_endpoints d r) hyz.2
  let eR := WiredBoxLocalized.boxActiveEdgeLE d hrR e
  have hrho : rho eR.1 = true := he
  have hedge : edgeIncl d R eR.1 = s(y, z) := by
    calc
      edgeIncl d R eR.1 =
          WiredBoxDifferential.boxActiveEdge d R eR := rfl
      _ = WiredBoxDifferential.boxActiveEdge d r e :=
        boxActiveEdgeLE_ambient d hrR e
      _ = s(WiredBoxDifferential.boxActiveEndU d r e,
          WiredBoxDifferential.boxActiveEndV d r e) :=
        WiredBoxDifferential.boxActiveEdge_eq_endpoints d r e
      _ = s(y, z) := by
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · rw [Sym2.eq_swap]
  rw [← hedge, extendEdge_eq_of_range]
  exact hrho


theorem openSubgraph_liftInner_le_liftOuter
    (d : Nat) {r R : Nat} (hrR : r <= R)
    (omega : ConfigSpace (boxGraph d R).edgeSet) :
    openSubgraph d
        (liftCfg (WiredBoxDifferential.boxActiveEdge d r)
          (restrictConfig (WiredBoxLocalized.boxActiveEdgeLE d hrR) omega)) <=
      openSubgraph d (liftCfg (WiredBoxDifferential.boxActiveEdge d R) omega) := by
  intro y z hyz
  rw [openSubgraph_adj] at hyz ⊢
  refine ⟨hyz.1, ?_⟩
  obtain ⟨e, he, hpair⟩ := exists_abstract_open_edge
    (WiredBoxDifferential.boxActiveEdge_eq_endpoints d r) hyz.2
  let eR := WiredBoxLocalized.boxActiveEdgeLE d hrR e
  have hopen : omega eR = true := he
  have hedge : WiredBoxDifferential.boxActiveEdge d R eR = s(y, z) := by
    calc
      WiredBoxDifferential.boxActiveEdge d R eR =
          WiredBoxDifferential.boxActiveEdge d r e :=
        boxActiveEdgeLE_ambient d hrR e
      _ = s(WiredBoxDifferential.boxActiveEndU d r e,
          WiredBoxDifferential.boxActiveEndV d r e) :=
        WiredBoxDifferential.boxActiveEdge_eq_endpoints d r e
      _ = s(y, z) := by
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · rw [Sym2.eq_swap]
  rw [← hedge, liftCfg_apply_edge
    (WiredBoxDifferential.boxActiveEdge_injective d R)]
  exact hopen


theorem innerCrossInd_le_fullOuterCrossInd
    (d n : Nat) (omega : ConfigSpace (boxGraph d (2 * n)).edgeSet) :
    WiredBoxLocalized.innerCrossInd d n omega <=
      AdaptiveCovLowerGeom.crossIndG
        (WiredBoxDifferential.boxActiveEdge d (2 * n)) 0 n omega := by
  unfold WiredBoxLocalized.innerCrossInd AdaptiveCovLowerGeom.crossIndG
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hi : ConnectedToSet d
      (liftCfg (WiredBoxDifferential.boxActiveEdge d n)
        (restrictConfig
          (WiredBoxLocalized.boxActiveEdgeLE d
            (WiredBoxLocalized.n_le_two_mul n)) omega))
      0 (vertexBoundary d n)
  · have hi' : restrictConfig
        (WiredBoxLocalized.boxActiveEdgeLE d
          (WiredBoxLocalized.n_le_two_mul n)) omega ∈
        crossEvent (WiredBoxDifferential.boxActiveEdge d n) 0
          (vertexBoundary d n) := hi
    rw [if_pos hi', if_pos]
    obtain ⟨b, hb, hconn⟩ := hi
    exact ⟨b, hb, hconn.mono (openSubgraph_liftInner_le_liftOuter d
      (WiredBoxLocalized.n_le_two_mul n) omega)⟩
  · have hi' : restrictConfig
        (WiredBoxLocalized.boxActiveEdgeLE d
          (WiredBoxLocalized.n_le_two_mul n)) omega ∉
        crossEvent (WiredBoxDifferential.boxActiveEdge d n) 0
          (vertexBoundary d n) := hi
    rw [if_neg hi']
    split <;> norm_num


end WiredBoxOffCentre
end OSSS
end StatMech
