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
import Def.StatisticalMechanics.Code.OSSS.WiredBoxOffCentre.Part3
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxOffCentre

open Lattice IsingFK RevealmentConstruction TreeComplete RevealmentTranslation CenteredFirstHit

open FK

open WiredBoxLocalized

@[simp] theorem centeredWithinToTransHom_val
    (d n k : Nat) (x : Site d)
    (hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n))
    (rho : ConfigSpace (Sym2 (boxVerts d (2 * n))))
    (y : centeredClosedBox x k) :
    ((centeredWithinToTransHom d n k x hsub rho y :
      fvs_transBoxVerts d (2 * k) x) : Site d) = y := rfl

@[simp] theorem centeredWithinToTransHom_center
    (d n k : Nat) (x : Site d)
    (hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n))
    (rho : ConfigSpace (Sym2 (boxVerts d (2 * n)))) :
    centeredWithinToTransHom d n k x hsub rho
        ⟨x, center_mem_centeredClosedBox x k⟩ =
      transBoxCenter d (2 * k) x := by
  apply Subtype.ext
  rfl


theorem outerInnerConn_subset_transShell
    (d n k : Nat) (x : Site d)
    (hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n))
    (rho : ConfigSpace (Sym2 (boxVerts d (2 * n))))
    (hconn : ConnectedToSet d
      (liftCfg (WiredBoxDifferential.boxActiveEdge d n)
        (restrictConfig
          (WiredBoxLocalized.boxActiveEdgeLE d
            (WiredBoxLocalized.n_le_two_mul n))
          (restrictActive (boxGraph d (2 * n)) rho)))
      x (centeredBoundary x k)) :
    ocd_innerRestrict (flc_incl hsub) rho ∈ transShellEvent d k x := by
  let omegaInner : ConfigSpace (Sym2 (Site d)) :=
    liftCfg (WiredBoxDifferential.boxActiveEdge d n)
      (restrictConfig
        (WiredBoxLocalized.boxActiveEdgeLE d
          (WiredBoxLocalized.n_le_two_mul n))
        (restrictActive (boxGraph d (2 * n)) rho))
  let omegaOuter : ConfigSpace (Sym2 (Site d)) := extendEdge d (2 * n) rho
  have hmono : openSubgraph d omegaInner <= openSubgraph d omegaOuter :=
    openSubgraph_liftInner_le_extendOuter d
      (WiredBoxLocalized.n_le_two_mul n) rho
  obtain ⟨y, hy, hxy⟩ := hconn
  have hxyOuter : Connected d omegaOuter x y := hxy.mono hmono
  obtain ⟨z, hz, hwithin⟩ :=
    connected_centeredBoundary_has_within hy hxyOuter
  let hom := centeredWithinToTransHom d n k x hsub rho
  have hreach := hwithin.map hom
  refine ⟨hom z, ?_, ?_⟩
  · change centeredRadius x (z : Site d) = k
    exact hz
  · simpa [hom, omegaOuter] using hreach


theorem wiredOuterInnerConn_le_theta_strict_of_domain
    (d n k : Nat) (x : Site d) (hx : x ∈ box d n)
    (hk1 : 1 <= k) (hkn : 2 * k < n)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n))
    (hdom :
      (∑ rho,
        (ocd_innerRestrict (flc_incl hsub) ⁻¹' transShellEvent d k x).indicator
            (fun _ => (1 : Real)) rho *
          wiredFkProb (boxGraph d (2 * n)) (boxBoundary d (2 * n))
            (1 - Real.exp (-beta)) q rho) <=
      WiredBoxLocalized.wiredOuterInnerTheta d q beta k) :
    WiredBoxLocalized.wiredOuterInnerConn d n q beta x k <=
      WiredBoxLocalized.wiredOuterInnerTheta d q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
    linarith
  have hp1 : p < 1 := by
    unfold p
    linarith [Real.exp_pos (-beta)]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  let obs : ConfigSpace (boxGraph d (2 * n)).edgeSet -> Real := fun eta =>
    if ConnectedToSet d
      (liftCfg (WiredBoxDifferential.boxActiveEdge d n)
        (restrictConfig
          (WiredBoxLocalized.boxActiveEdgeLE d
            (WiredBoxLocalized.n_le_two_mul n)) eta))
      x (centeredBoundary x k) then 1 else 0
  have hparam : FK.betaParams
      (fun _ : Sym2 (boxVerts d (2 * n)) => (1 : Real)) beta = fun _ => p := by
    funext e
    simp [FK.betaParams, p]
  have hmean := activeBCMean_boundaryClique_eq_wired
    (boxGraph d (2 * n)) (boxBoundary d (2 * n)) hp hp1 hq0 obs
  have hleft : WiredBoxLocalized.wiredOuterInnerConn d n q beta x k =
      ∑ rho, obs (restrictActive (boxGraph d (2 * n)) rho) *
        wiredFkProb (boxGraph d (2 * n)) (boxBoundary d (2 * n)) p q rho := by
    unfold WiredBoxLocalized.wiredOuterInnerConn
    rw [hparam]
    change FK.activeBCMean (boxGraph d (2 * n))
      (Lattice.boundaryCliqueGraph (boxBoundary d (2 * n))) (fun _ => p) q obs = _
    exact hmean
  rw [hleft]
  have hEventLe :
      (∑ rho, obs (restrictActive (boxGraph d (2 * n)) rho) *
        wiredFkProb (boxGraph d (2 * n)) (boxBoundary d (2 * n)) p q rho) <=
      ∑ rho,
        (ocd_innerRestrict (flc_incl hsub) ⁻¹' transShellEvent d k x).indicator
            (fun _ => (1 : Real)) rho *
          wiredFkProb (boxGraph d (2 * n)) (boxBoundary d (2 * n)) p q rho := by
    apply Finset.sum_le_sum
    intro rho _
    apply mul_le_mul_of_nonneg_right
    · unfold obs
      by_cases hc : ConnectedToSet d
          (liftCfg (WiredBoxDifferential.boxActiveEdge d n)
            (restrictConfig
              (WiredBoxLocalized.boxActiveEdgeLE d
                (WiredBoxLocalized.n_le_two_mul n))
              (restrictActive (boxGraph d (2 * n)) rho)))
          x (centeredBoundary x k)
      · rw [if_pos hc, Set.indicator_of_mem]
        exact outerInnerConn_subset_transShell d n k x hsub rho hc
      · rw [if_neg hc]
        exact Set.indicator_nonneg (fun _ => by norm_num) _
    · exact wiredFkProb_nonneg (boxGraph d (2 * n))
        (boxBoundary d (2 * n)) hp hp1 hq0 rho
  simpa [p] using hEventLe.trans hdom

theorem centeredRadius_transEquiv (d R : Nat) (x : Site d)
    (y : boxVerts d R) :
    centeredRadius x (fvs_transEquiv d R x y : Site d) =
      siteRadius (y : Site d) := by
  unfold centeredRadius
  rw [fvs_transEquiv_val]
  congr 1
  funext i
  simp [Pi.add_apply]

@[simp] theorem transEquiv_boxOrigin (d R : Nat) (x : Site d) :
    fvs_transEquiv d R x (IsingFK.boxOrigin d R) = transBoxCenter d R x := by
  apply Subtype.ext
  funext i
  simp [transBoxCenter, IsingFK.boxOrigin, Percolation.origin]


theorem reCfgIso_preimage_centeredShellEvent (d k : Nat) (x : Site d) :
    reCfgIso (fvs_transEquiv d (2 * k) x) ⁻¹' centeredShellEvent d k =
      transShellEvent d k x := by
  ext rho
  constructor
  · rintro ⟨y, hy, hreach⟩
    let iso := fvs_openSubIso (boxGraph d (2 * k))
      (fvs_transBoxGraph d (2 * k) x) (fvs_transEquiv d (2 * k) x)
      (fvs_transEquiv_adj d (2 * k) x) rho
    refine ⟨fvs_transEquiv d (2 * k) x y, ?_, ?_⟩
    · rw [centeredRadius_transEquiv]
      exact hy
    · rw [← transEquiv_boxOrigin]
      exact iso.reachable_iff.mpr hreach
  · rintro ⟨y, hy, hreach⟩
    let iso := fvs_openSubIso (boxGraph d (2 * k))
      (fvs_transBoxGraph d (2 * k) x) (fvs_transEquiv d (2 * k) x)
      (fvs_transEquiv_adj d (2 * k) x) rho
    let y0 : boxVerts d (2 * k) := (fvs_transEquiv d (2 * k) x).symm y
    refine ⟨y0, ?_, ?_⟩
    · have hrad := centeredRadius_transEquiv d (2 * k) x y0
      have hyEq : fvs_transEquiv d (2 * k) x y0 = y :=
        (fvs_transEquiv d (2 * k) x).apply_symm_apply y
      rw [hyEq] at hrad
      exact hrad.symm.trans hy
    · apply iso.reachable_iff.mp
      change (openSub (fvs_transBoxGraph d (2 * k) x) rho).Reachable
        (fvs_transEquiv d (2 * k) x (IsingFK.boxOrigin d (2 * k)))
        (fvs_transEquiv d (2 * k) x y0)
      rw [transEquiv_boxOrigin]
      simpa [y0] using hreach


theorem transShellEvent_mass_eq_centered
    (d k : Nat) (x : Site d) (p q : Real) :
    (∑ rho,
      (transShellEvent d k x).indicator (fun _ => (1 : Real)) rho *
        wiredFkProb (fvs_transBoxGraph d (2 * k) x)
          (fvs_transBoxBoundary d (2 * k) x) p q rho) =
    ∑ eta,
      (centeredShellEvent d k).indicator (fun _ => (1 : Real)) eta *
        wiredFkProb (boxGraph d (2 * k)) (boxBoundary d (2 * k)) p q eta := by
  have htransport := cdc_eventMassProb_reCfgIso_inv
    (fvs_transEquiv d (2 * k) x)
    (wiredFkProb (boxGraph d (2 * k)) (boxBoundary d (2 * k)) p q)
    (wiredFkProb (fvs_transBoxGraph d (2 * k) x)
      (fvs_transBoxBoundary d (2 * k) x) p q)
    (fun rho => fvs_wiredFkProb_reCfgIso
      (boxGraph d (2 * k)) (fvs_transBoxGraph d (2 * k) x)
      (boxBoundary d (2 * k)) (fvs_transBoxBoundary d (2 * k) x)
      (fvs_transEquiv d (2 * k) x)
      (fvs_transEquiv_adj d (2 * k) x)
      (fvs_transEquiv_boundary d (2 * k) x) p q rho)
    (centeredShellEvent d k)
  rwa [reCfgIso_preimage_centeredShellEvent] at htransport


theorem transShellEvent_domain_dominated
    (d n k : Nat) (x : Site d) (hx : x ∈ box d n)
    (hk1 : 1 <= k) (hkn : 2 * k < n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    (∑ rho,
      (ocd_innerRestrict
        (flc_incl (show fvs_transBox d (2 * k) x ⊆ box d (2 * n) by
          intro y hy i
          have hyi : ((y - x) i).natAbs <= 2 * k := hy i
          have hxi : (x i).natAbs <= n := hx i
          have hEq : y i = (y i - x i) + x i := by ring
          calc
            (y i).natAbs = ((y i - x i) + x i).natAbs := by rw [← hEq]
            _ <= (y i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _
            _ = ((y - x) i).natAbs + (x i).natAbs := by simp [Pi.sub_apply]
            _ <= 2 * k + n := Nat.add_le_add hyi hxi
            _ <= 2 * n := by omega)) ⁻¹' transShellEvent d k x).indicator
          (fun _ => (1 : Real)) rho *
        wiredFkProb (boxGraph d (2 * n)) (boxBoundary d (2 * n)) p q rho) <=
    ∑ eta,
      (centeredShellEvent d k).indicator (fun _ => (1 : Real)) eta *
        wiredFkProb (boxGraph d (2 * k)) (boxBoundary d (2 * k)) p q eta := by
  let hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n) := by
    intro y hy i
    have hyi : ((y - x) i).natAbs <= 2 * k := hy i
    have hxi : (x i).natAbs <= n := hx i
    have hEq : y i = (y i - x i) + x i := by ring
    calc
      (y i).natAbs = ((y i - x i) + x i).natAbs := by rw [← hEq]
      _ <= (y i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _
      _ = ((y - x) i).natAbs + (x i).natAbs := by simp [Pi.sub_apply]
      _ <= 2 * k + n := Nat.add_le_add hyi hxi
      _ <= 2 * n := by omega
  have hxdeep : x ∈ box d (2 * n - 2 * k - 1) := by
    apply box_mono d (show n <= 2 * n - 2 * k - 1 by omega)
    exact hx
  have hmargin := ocs_wired_margin d (2 * k) (2 * n) x hxdeep
    (show 2 * k + 1 <= 2 * n by omega) hsub
  have hdom := ocd_latticeWired_inner_dominated
    (Sin := fvs_transBox d (2 * k) x) (Sout := box d (2 * n))
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    (boxBoundary d (2 * n)) (fvs_transBoxBoundary d (2 * k) x)
    hmargin (flc_hbdryIn_transBox (show 1 <= 2 * k by omega) x)
    hp hp1 hq (transShellEvent_increasing d k x)
  change (∑ rho,
      (ocd_innerRestrict (flc_incl hsub) ⁻¹' transShellEvent d k x).indicator
          (fun _ => (1 : Real)) rho *
        wiredFkProb (boxGraph d (2 * n)) (boxBoundary d (2 * n)) p q rho) <=
    ∑ eta,
      (transShellEvent d k x).indicator (fun _ => (1 : Real)) eta *
        wiredFkProb (fvs_transBoxGraph d (2 * k) x)
          (fvs_transBoxBoundary d (2 * k) x) p q eta at hdom
  rw [transShellEvent_mass_eq_centered d k x p q] at hdom
  simpa [hsub] using hdom


theorem wiredOuterInnerConn_le_theta_strict
    (d n k : Nat) (x : Site d) (hx : x ∈ box d n)
    (hk1 : 1 <= k) (hkn : 2 * k < n)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    WiredBoxLocalized.wiredOuterInnerConn d n q beta x k <=
      WiredBoxLocalized.wiredOuterInnerTheta d q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
    linarith
  have hp1 : p < 1 := by
    unfold p
    linarith [Real.exp_pos (-beta)]
  let hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n) := by
    intro y hy i
    have hyi : ((y - x) i).natAbs <= 2 * k := hy i
    have hxi : (x i).natAbs <= n := hx i
    have hEq : y i = (y i - x i) + x i := by ring
    calc
      (y i).natAbs = ((y i - x i) + x i).natAbs := by rw [← hEq]
      _ <= (y i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _
      _ = ((y - x) i).natAbs + (x i).natAbs := by simp [Pi.sub_apply]
      _ <= 2 * k + n := Nat.add_le_add hyi hxi
      _ <= 2 * n := by omega
  have hdomain := transShellEvent_domain_dominated
    d n k x hx hk1 hkn hp hp1 hq
  have htheta := wiredOuterInnerTheta_eq_centeredShellMass
    d k hk1 q beta hq hbeta
  have hdomTheta :
      (∑ rho,
        (ocd_innerRestrict (flc_incl hsub) ⁻¹' transShellEvent d k x).indicator
            (fun _ => (1 : Real)) rho *
          wiredFkProb (boxGraph d (2 * n)) (boxBoundary d (2 * n)) p q rho) <=
      WiredBoxLocalized.wiredOuterInnerTheta d q beta k := by
    calc
      _ <= ∑ eta,
          (centeredShellEvent d k).indicator (fun _ => (1 : Real)) eta *
            wiredFkProb (boxGraph d (2 * k)) (boxBoundary d (2 * k)) p q eta := by
          simpa [hsub] using hdomain
      _ = WiredBoxLocalized.wiredOuterInnerTheta d q beta k := by
          simpa [p] using htheta.symm
  exact wiredOuterInnerConn_le_theta_strict_of_domain
    d n k x hx hk1 hkn q beta hq hbeta hsub (by simpa [p] using hdomTheta)

theorem wiredOuterInner_strictTranslationComparison
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    forall x, x ∈ WiredBoxDifferential.osssBoxFinset d n -> forall k,
      k ∈ Finset.Icc 1 (n / 2) -> 2 * k < n ->
      WiredBoxLocalized.wiredOuterInnerConn d n q beta x k <=
        WiredBoxLocalized.wiredOuterInnerTheta d q beta k := by
  intro x hx k hk hstrict
  apply wiredOuterInnerConn_le_theta_strict d n k x
  · simpa [WiredBoxDifferential.mem_osssBoxFinset] using hx
  · exact (Finset.mem_Icc.mp hk).1
  · exact hstrict
  · exact hq
  · exact hbeta


theorem wiredOuterInnerDenom_le_eight_sig
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    WiredBoxLocalized.wiredOuterInnerDenom d n q beta <=
      8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real) := by
  exact WiredBoxLocalized.wiredOuterInnerDenom_le_eight_sig_of_strict_comparison
    d n q beta hq hbeta
      (wiredOuterInner_strictTranslationComparison d n q beta hq hbeta)


theorem wired_outer_inner_hcov_sharp
    (d n : Nat) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    Lindeberg.mean
        (activeBCProb (boxGraph d (2 * n))
          (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
          (betaParams (fun _ => 1) beta) q)
        (WiredBoxLocalized.innerCrossInd d n) *
      (1 - Lindeberg.mean
        (activeBCProb (boxGraph d (2 * n))
          (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
          (betaParams (fun _ => 1) beta) q)
        (WiredBoxLocalized.innerCrossInd d n)) /
          (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real)) <=
      ∑ e, Lindeberg.cov
        (activeBCProb (boxGraph d (2 * n))
          (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
          (betaParams (fun _ => 1) beta) q)
        (WiredBoxLocalized.innerCrossInd d n) (Lindeberg.coord e) := by
  let mu := activeBCProb (boxGraph d (2 * n))
    (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
    (betaParams (fun _ => 1) beta) q
  let theta := Lindeberg.mean mu (WiredBoxLocalized.innerCrossInd d n)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : forall e : Sym2 (boxVerts d (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (activeBCProb_pos _ _ (betaParams_pos hJ hbeta)
      (betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    activeBCProb_sum_eq_one _ _ (betaParams_pos hJ hbeta)
      (betaParams_lt_one (fun _ => 1) beta) hq0
  have htheta0 : 0 <= theta := by
    unfold theta Lindeberg.mean
    apply Finset.sum_nonneg
    intro omega _
    apply mul_nonneg
    · unfold WiredBoxLocalized.innerCrossInd AdaptiveCovLowerGeom.crossIndG
      rw [Set.indicator_apply]
      split_ifs <;> norm_num
    · exact hmu0 omega
  have htheta1 : theta <= 1 := by
    calc
      theta <= Lindeberg.mean mu (fun _ => (1 : Real)) := by
        unfold theta Lindeberg.mean
        apply Finset.sum_le_sum
        intro omega _
        apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
        unfold WiredBoxLocalized.innerCrossInd AdaptiveCovLowerGeom.crossIndG
        rw [Set.indicator_apply]
        split_ifs <;> norm_num
      _ = 1 := Lindeberg.mean_const mu hmu1 1
  have hnum : 0 <= theta * (1 - theta) :=
    mul_nonneg htheta0 (sub_nonneg.mpr htheta1)
  have hDpos := WiredBoxLocalized.wiredOuterInnerDenom_pos
    d n hn q beta hq hbeta
  have hDle := wiredOuterInnerDenom_le_eight_sig d n q beta hq hbeta
  have hfrac : theta * (1 - theta) /
      (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real)) <=
      theta * (1 - theta) /
        WiredBoxLocalized.wiredOuterInnerDenom d n q beta :=
    div_le_div_of_nonneg_left hnum hDpos hDle
  have hbase := WiredBoxLocalized.wired_outer_inner_hcov_geom
    d n hn q beta hq hbeta
  exact hfrac.trans (by simpa [mu, theta] using hbase)


theorem wired_outer_inner_differential_sharp
    (d n : Nat) (hd : 1 <= d) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    exists cR : Real, 0 < cR ∧
      cR * (Lindeberg.mean
          (activeBCProb (boxGraph d (2 * n))
            (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
            (betaParams (fun _ => 1) beta) q)
          (WiredBoxLocalized.innerCrossInd d n) *
        (1 - Lindeberg.mean
          (activeBCProb (boxGraph d (2 * n))
            (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
            (betaParams (fun _ => 1) beta) q)
          (WiredBoxLocalized.innerCrossInd d n)) /
            (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta /
              (n : Real))) <=
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
        (betaParams (fun _ => 1) b) q
        (WiredBoxLocalized.innerCrossInd d n)) beta := by
  letI : Nonempty (boxGraph d (2 * n)).edgeSet :=
    WiredBoxDifferential.boxGraph_edgeSet_nonempty d (2 * n) hd (by omega)
  let G := boxGraph d (2 * n)
  let C := WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)
  let J : Sym2 (boxVerts d (2 * n)) -> Real := fun _ => 1
  let mu := activeBCProb G C (betaParams J beta) q
  let f := WiredBoxLocalized.innerCrossInd d n
  have hJ : forall e, 0 < J e := fun _ => by simp [J]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hcov : Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) /
        (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta /
          (n : Real)) <=
      ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
    simpa [G, C, J, mu, f] using
      wired_outer_inner_hcov_sharp d n hn q beta hq hbeta
  have hpos : forall omega, 0 < mu omega :=
    activeBCProb_pos G C (betaParams_pos hJ hbeta)
      (betaParams_lt_one J beta) hq0
  have hmu1 : ∑ omega, mu omega = 1 :=
    activeBCProb_sum_eq_one G C (betaParams_pos hJ hbeta)
      (betaParams_lt_one J beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    activeBCProb_FKGLatticeCondition G C (betaParams_pos hJ hbeta)
      (betaParams_lt_one J beta) hq
  have hf : Monotone f := WiredBoxLocalized.innerCrossInd_monotone d n
  have hcov0 : forall e : G.edgeSet,
      0 <= activeBCCov G C (betaParams J beta) q f
        (Lindeberg.coord e) := by
    intro e
    rw [← ActiveBoundaryDifferential.cov_activeBC_eq]
    exact LindebergTree.cov_coord_nonneg hpos hmu1 hFKG hf e
  have hderiv := hasDerivAt_activeBCMean_beta_sum G C hJ hbeta hq0 f
  have hderivEq :
      deriv (fun b => activeBCMean G C (betaParams J b) q f) beta =
        ∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(beta * J e.1)))) *
          activeBCCov G C (betaParams J beta) q f
            (Lindeberg.coord e) := by
    rw [hderiv.deriv]
    simp only [betaParams]
  obtain ⟨cR, hcR, hRusso⟩ :=
    RussoPrefactor.rp_differential_lower_weighted_beta
      (fun e : G.edgeSet => J e.1)
      (fun e => activeBCCov G C (betaParams J beta) q f
        (Lindeberg.coord e)) beta
      (deriv (fun b => activeBCMean G C (betaParams J b) q f) beta)
      (fun e => hJ e.1) hbeta hcov0 hderivEq
  refine ⟨cR, hcR, ?_⟩
  have hmain := (mul_le_mul_of_nonneg_left hcov hcR.le).trans hRusso
  simpa [G, C, J, mu, f] using hmain


theorem wired_outer_inner_differential_sharp_uniform
    (d n : Nat) (hn : 1 <= n) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    Lindeberg.mean
          (activeBCProb (boxGraph d (2 * n))
            (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
            (betaParams (fun _ => 1) beta) q)
          (WiredBoxLocalized.innerCrossInd d n) *
        (1 - Lindeberg.mean
          (activeBCProb (boxGraph d (2 * n))
            (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
            (betaParams (fun _ => 1) beta) q)
          (WiredBoxLocalized.innerCrossInd d n)) /
            (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta /
              (n : Real)) <=
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
        (betaParams (fun _ => 1) b) q
        (WiredBoxLocalized.innerCrossInd d n)) beta := by
  let G := boxGraph d (2 * n)
  let C := WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)
  let J : Sym2 (boxVerts d (2 * n)) -> Real := fun _ => 1
  let mu := activeBCProb G C (betaParams J beta) q
  let f := WiredBoxLocalized.innerCrossInd d n
  have hJ : forall e, 0 < J e := fun _ => by simp [J]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hcov : Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) /
        (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta /
          (n : Real)) <=
      ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
    simpa [G, C, J, mu, f] using
      wired_outer_inner_hcov_sharp d n hn q beta hq hbeta
  have hpos : forall omega, 0 < mu omega :=
    activeBCProb_pos G C (betaParams_pos hJ hbeta)
      (betaParams_lt_one J beta) hq0
  have hmu1 : ∑ omega, mu omega = 1 :=
    activeBCProb_sum_eq_one G C (betaParams_pos hJ hbeta)
      (betaParams_lt_one J beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    activeBCProb_FKGLatticeCondition G C (betaParams_pos hJ hbeta)
      (betaParams_lt_one J beta) hq
  have hf : Monotone f := WiredBoxLocalized.innerCrossInd_monotone d n
  have hcov0 : forall e : G.edgeSet,
      0 <= activeBCCov G C (betaParams J beta) q f
        (Lindeberg.coord e) := by
    intro e
    rw [← ActiveBoundaryDifferential.cov_activeBC_eq]
    exact LindebergTree.cov_coord_nonneg hpos hmu1 hFKG hf e
  have hderiv := hasDerivAt_activeBCMean_beta_sum G C hJ hbeta hq0 f
  have hderivEq :
      deriv (fun b => activeBCMean G C (betaParams J b) q f) beta =
        ∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(beta * J e.1)))) *
          activeBCCov G C (betaParams J beta) q f
            (Lindeberg.coord e) := by
    rw [hderiv.deriv]
    simp only [betaParams]
  have hpref : forall e : G.edgeSet,
      (1 : Real) <= J e.1 / (1 - Real.exp (-(beta * J e.1))) := by
    intro e
    have hden : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    simp only [J, mul_one]
    rw [le_div_iff₀ hden]
    linarith [Real.exp_pos (-beta)]
  have hRusso :
      ∑ e : G.edgeSet, activeBCCov G C (betaParams J beta) q f
          (Lindeberg.coord e) <=
        deriv (fun b => activeBCMean G C (betaParams J b) q f) beta := by
    rw [hderivEq]
    simpa using RussoPrefactor.rp_prefactor_extraction
      (fun e : G.edgeSet => J e.1 / (1 - Real.exp (-(beta * J e.1))))
      (fun e => activeBCCov G C (betaParams J beta) q f
        (Lindeberg.coord e)) 1 hpref hcov0
  have hmain := hcov.trans (by
    simpa [ActiveBoundaryDifferential.cov_activeBC_eq] using hRusso)
  simpa [G, C, J, mu, f] using hmain


theorem wired_outer_inner_one_sub_lower
    (d n : Nat) (hn : 1 <= n) (q beta beta0 : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) (hbeta0 : beta <= beta0) :
    (ActiveEdgeDifferential.incidentEdges
        (WiredBoxDifferential.boxActiveEndU d (2 * n))
        (WiredBoxDifferential.boxActiveEndV d (2 * n)) 0).prod
        (fun _ => Real.exp (-beta0)) <=
      1 - Lindeberg.mean
        (activeBCProb (boxGraph d (2 * n))
          (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
          (betaParams (fun _ => 1) beta) q)
        (WiredBoxLocalized.innerCrossInd d n) := by
  let G := boxGraph d (2 * n)
  let C := WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)
  let J : Sym2 (boxVerts d (2 * n)) -> Real := fun _ => 1
  let mu := activeBCProb G C (betaParams J beta) q
  let full := AdaptiveCovLowerGeom.crossIndG
    (WiredBoxDifferential.boxActiveEdge d (2 * n)) 0 n
  have hJ : forall e, 0 < J e := fun _ => by simp [J]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (activeBCProb_pos G C (betaParams_pos hJ hbeta)
      (betaParams_lt_one J beta) hq0 omega).le
  have hoB : (0 : Site d) ∉ vertexBoundary d n := by
    simpa using WiredBoxDifferential.origin_not_mem_osssBoundaryFinset d n
  have hfull := ActiveBoundaryDifferential.activeBC_cross_one_sub_lower
    G C J hJ q beta beta0 hq hbeta hbeta0
    (WiredBoxDifferential.boxActiveEdge_eq_endpoints d (2 * n))
    (0 : Site d) (vertexBoundary d n) hoB
  have hfull' :
      (ActiveEdgeDifferential.incidentEdges
          (WiredBoxDifferential.boxActiveEndU d (2 * n))
          (WiredBoxDifferential.boxActiveEndV d (2 * n)) 0).prod
          (fun _ => Real.exp (-beta0)) <=
        1 - Lindeberg.mean mu full := by
    simpa [G, C, J, mu, full, AdaptiveCovLowerGeom.crossIndG] using hfull
  have hmean : Lindeberg.mean mu (WiredBoxLocalized.innerCrossInd d n) <=
      Lindeberg.mean mu full := by
    unfold Lindeberg.mean
    apply Finset.sum_le_sum
    intro omega _
    apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
    exact innerCrossInd_le_fullOuterCrossInd d n omega
  simpa [G, C, J, mu] using hfull'.trans (by linarith)


theorem wiredOuterIncident_card_le (d R : Nat) :
    (ActiveEdgeDifferential.incidentEdges
        (WiredBoxDifferential.boxActiveEndU d R)
        (WiredBoxDifferential.boxActiveEndV d R) 0).card <= 2 * d := by
  let I := ActiveEdgeDifferential.incidentEdges
    (WiredBoxDifferential.boxActiveEndU d R)
    (WiredBoxDifferential.boxActiveEndV d R) 0
  calc
    I.card <= ((hypercubicLattice d).incidenceFinset (0 : Site d)).card := by
      apply Finset.card_le_card_of_injOn
        (WiredBoxDifferential.boxActiveEdge d R)
      · intro e he
        rw [Finset.mem_coe, SimpleGraph.mem_incidenceFinset]
        change e ∈ ActiveEdgeDifferential.incidentEdges
          (WiredBoxDifferential.boxActiveEndU d R)
          (WiredBoxDifferential.boxActiveEndV d R) 0 at he
        rw [ActiveEdgeDifferential.incidentEdges, Finset.mem_filter] at he
        refine ⟨?_, ?_⟩
        · rw [WiredBoxDifferential.boxActiveEdge_eq_endpoints,
            SimpleGraph.mem_edgeSet]
          exact WiredBoxDifferential.boxActiveEnd_adj d R e
        · rw [WiredBoxDifferential.boxActiveEdge_eq_endpoints]
          rcases he.2 with hu | hv
          · rw [hu]
            exact Sym2.mem_mk_left _ _
          · rw [hv]
            exact Sym2.mem_mk_right _ _
      · intro a ha b hb hab
        exact WiredBoxDifferential.boxActiveEdge_injective d R hab
    _ = (hypercubicLattice d).degree (0 : Site d) :=
      SimpleGraph.card_incidenceFinset_eq_degree _ _
    _ <= 2 * d := degree_le d 0


theorem wiredOuterIncident_prod_lower
    (d R : Nat) (beta0 : Real) (hbeta0 : 0 <= beta0) :
    Real.exp (-beta0) ^ (2 * d) <=
      (ActiveEdgeDifferential.incidentEdges
        (WiredBoxDifferential.boxActiveEndU d R)
        (WiredBoxDifferential.boxActiveEndV d R) 0).prod
        (fun _ => Real.exp (-beta0)) := by
  have ha0 : 0 <= Real.exp (-beta0) := (Real.exp_pos _).le
  have ha1 : Real.exp (-beta0) <= 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hpow := pow_le_pow_of_le_one ha0 ha1 (wiredOuterIncident_card_le d R)
  simpa [Finset.prod_const] using hpow


theorem wired_outer_inner_differential_inequality
    (d n : Nat) (hd : 1 <= d) (hn : 1 <= n)
    (q beta beta0 : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hbeta0 : beta <= beta0) :
    exists c : Real, 0 < c ∧
      c * (Lindeberg.mean
          (activeBCProb (boxGraph d (2 * n))
            (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
            (betaParams (fun _ => 1) beta) q)
          (WiredBoxLocalized.innerCrossInd d n) /
            (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta /
              (n : Real))) <=
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
        (betaParams (fun _ => 1) b) q
        (WiredBoxLocalized.innerCrossInd d n)) beta := by
  let mu := activeBCProb (boxGraph d (2 * n))
    (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
    (betaParams (fun _ => 1) beta) q
  let theta := Lindeberg.mean mu (WiredBoxLocalized.innerCrossInd d n)
  let D := 8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real)
  let kappa := (ActiveEdgeDifferential.incidentEdges
      (WiredBoxDifferential.boxActiveEndU d (2 * n))
      (WiredBoxDifferential.boxActiveEndV d (2 * n)) 0).prod
      (fun _ => Real.exp (-beta0))
  obtain ⟨cR, hcR, hlog⟩ := wired_outer_inner_differential_sharp
    d n hd hn q beta hq hbeta
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : forall e : Sym2 (boxVerts d (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (activeBCProb_pos _ _ (betaParams_pos hJ hbeta)
      (betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have htheta : 0 <= theta := by
    unfold theta Lindeberg.mean
    apply Finset.sum_nonneg
    intro omega _
    apply mul_nonneg
    · unfold WiredBoxLocalized.innerCrossInd AdaptiveCovLowerGeom.crossIndG
      rw [Set.indicator_apply]
      split_ifs <;> norm_num
    · exact hmu0 omega
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : 0 < D := by
    unfold D
    have hSig := WiredBoxLocalized.wiredOuterInnerSig_pos
      d n hn q beta hq hbeta
    positivity
  have hkappa : 0 < kappa := by
    unfold kappa
    exact Finset.prod_pos fun e he => Real.exp_pos _
  have hgap : kappa <= 1 - theta := by
    simpa [kappa, theta, mu] using
      wired_outer_inner_one_sub_lower d n hn q beta beta0
        hq hbeta hbeta0
  have hlog' : cR * (theta * (1 - theta) / D) <=
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
        (betaParams (fun _ => 1) b) q
        (WiredBoxLocalized.innerCrossInd d n)) beta := by
    simpa [theta, D, mu] using hlog
  obtain ⟨hc, hmain⟩ := ActiveEdgeDifferential.absorb_cross_complement
    htheta hD hkappa hcR hgap hlog'
  exact ⟨cR * kappa, hc, by simpa [theta, D, mu] using hmain⟩


theorem wired_outer_inner_differential_uniform
    (d n : Nat) (hn : 1 <= n) (q beta beta0 : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) (hbeta0 : beta <= beta0) :
    (ActiveEdgeDifferential.incidentEdges
        (WiredBoxDifferential.boxActiveEndU d (2 * n))
        (WiredBoxDifferential.boxActiveEndV d (2 * n)) 0).prod
        (fun _ => Real.exp (-beta0)) *
      (Lindeberg.mean
          (activeBCProb (boxGraph d (2 * n))
            (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
            (betaParams (fun _ => 1) beta) q)
          (WiredBoxLocalized.innerCrossInd d n) /
        (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta /
          (n : Real))) <=
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
        (betaParams (fun _ => 1) b) q
        (WiredBoxLocalized.innerCrossInd d n)) beta := by
  let mu := activeBCProb (boxGraph d (2 * n))
    (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
    (betaParams (fun _ => 1) beta) q
  let theta := Lindeberg.mean mu (WiredBoxLocalized.innerCrossInd d n)
  let D := 8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real)
  let kappa := (ActiveEdgeDifferential.incidentEdges
      (WiredBoxDifferential.boxActiveEndU d (2 * n))
      (WiredBoxDifferential.boxActiveEndV d (2 * n)) 0).prod
      (fun _ => Real.exp (-beta0))
  have hlog := wired_outer_inner_differential_sharp_uniform
    d n hn q beta hq hbeta
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : forall e : Sym2 (boxVerts d (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (activeBCProb_pos _ _ (betaParams_pos hJ hbeta)
      (betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have htheta : 0 <= theta := by
    unfold theta Lindeberg.mean
    apply Finset.sum_nonneg
    intro omega _
    apply mul_nonneg
    · unfold WiredBoxLocalized.innerCrossInd AdaptiveCovLowerGeom.crossIndG
      rw [Set.indicator_apply]
      split_ifs <;> norm_num
    · exact hmu0 omega
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : 0 < D := by
    unfold D
    have hSig := WiredBoxLocalized.wiredOuterInnerSig_pos
      d n hn q beta hq hbeta
    positivity
  have hkappa : 0 < kappa := by
    unfold kappa
    exact Finset.prod_pos fun e he => Real.exp_pos _
  have hgap : kappa <= 1 - theta := by
    simpa [kappa, theta, mu] using
      wired_outer_inner_one_sub_lower d n hn q beta beta0
        hq hbeta hbeta0
  have hlog' : (1 : Real) * (theta * (1 - theta) / D) <=
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
        (betaParams (fun _ => 1) b) q
        (WiredBoxLocalized.innerCrossInd d n)) beta := by
    simpa [theta, D, mu] using hlog
  obtain ⟨_, hmain⟩ := ActiveEdgeDifferential.absorb_cross_complement
    htheta hD hkappa (show (0 : Real) < 1 by norm_num) hgap hlog'
  simpa [theta, D, kappa, mu] using hmain


theorem wired_outer_inner_differential_uniform_box
    (d n : Nat) (hn : 1 <= n) (q beta beta0 : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) (hbeta0 : beta <= beta0) :
    Real.exp (-beta0) ^ (2 * d) *
      (Lindeberg.mean
          (activeBCProb (boxGraph d (2 * n))
            (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
            (betaParams (fun _ => 1) beta) q)
          (WiredBoxLocalized.innerCrossInd d n) /
        (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta /
          (n : Real))) <=
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
        (betaParams (fun _ => 1) b) q
        (WiredBoxLocalized.innerCrossInd d n)) beta := by
  let mu := activeBCProb (boxGraph d (2 * n))
    (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n))
    (betaParams (fun _ => 1) beta) q
  let theta := Lindeberg.mean mu (WiredBoxLocalized.innerCrossInd d n)
  let D := 8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real)
  let kappa := (ActiveEdgeDifferential.incidentEdges
      (WiredBoxDifferential.boxActiveEndU d (2 * n))
      (WiredBoxDifferential.boxActiveEndV d (2 * n)) 0).prod
      (fun _ => Real.exp (-beta0))
  have hbase := wired_outer_inner_differential_uniform
    d n hn q beta beta0 hq hbeta hbeta0
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : forall e : Sym2 (boxVerts d (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (activeBCProb_pos _ _ (betaParams_pos hJ hbeta)
      (betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have htheta : 0 <= theta := by
    unfold theta Lindeberg.mean
    apply Finset.sum_nonneg
    intro omega _
    apply mul_nonneg
    · unfold WiredBoxLocalized.innerCrossInd AdaptiveCovLowerGeom.crossIndG
      rw [Set.indicator_apply]
      split_ifs <;> norm_num
    · exact hmu0 omega
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : 0 < D := by
    unfold D
    have hSig := WiredBoxLocalized.wiredOuterInnerSig_pos
      d n hn q beta hq hbeta
    positivity
  have hc0le : Real.exp (-beta0) ^ (2 * d) <= kappa := by
    simpa [kappa] using wiredOuterIncident_prod_lower
      d (2 * n) beta0 (le_trans hbeta.le hbeta0)
  have hscale : Real.exp (-beta0) ^ (2 * d) * (theta / D) <=
      kappa * (theta / D) :=
    mul_le_mul_of_nonneg_right hc0le (div_nonneg htheta hD.le)
  exact hscale.trans (by simpa [theta, D, kappa, mu] using hbase)

end WiredBoxOffCentre
end OSSS
end StatMech
