/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Def.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part10
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem triangularTransShellFullEvent_increasing
    (R k : Nat) (x : Site 2) :
    IsIncreasing (triangularTransShellFullEvent R k x) := by
  intro omega eta home hmem
  obtain ⟨y, hy, hreach⟩ := hmem
  refine ⟨y, hy, hreach.mono ?_⟩
  intro a b hab
  rw [FK.openSub_adj] at hab ⊢
  refine ⟨hab.1, ?_⟩
  apply Bool.eq_true_of_true_le
  simpa [hab.2] using home s(a, b)

theorem triangularBufferedTransShellEvent_increasing
    (k : Nat) (x : Site 2) :
    IsIncreasing (triangularBufferedTransShellEvent k x) := by
  intro omega eta home hmem
  exact triangularTransShellFullEvent_increasing (2 * k) k x
    (fun e => home _) hmem

theorem triangularTransFullMass_eq_outerInnerTheta
    (k : Nat) (hk : 1 ≤ k) (x : Site 2) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    finiteWiredEventMass (triangularTransBoxGraph (2 * k) x)
        (triangularTransBoxBoundary (2 * k) x)
        (1 - Real.exp (-beta)) q
        (triangularTransShellFullEvent (2 * k) k x) =
      triangularOuterInnerTheta q beta k := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  have htrans := triangularTransShellEvent_betaMean_eq_centeredFullMass
    (2 * k) k x q beta (zero_lt_one.trans_le hq) hbeta
  have hparam : FK.betaParams
      (fun _ : Sym2 (TriangularTransBoxVertex (2 * k) x) => 1) beta =
      fun _ => 1 - Real.exp (-beta) := by
    funext e
    simp [FK.betaParams]
  rw [hparam] at htrans
  rw [FK.activeBCMean_boundaryClique_eq_wired
    (triangularTransBoxGraph (2 * k) x)
    (triangularTransBoxBoundary (2 * k) x)
    hp hp1 (zero_lt_one.trans_le hq)] at htrans
  rw [← triangularCenteredFullMass_eq_outerInnerTheta
    k hk q beta hq hbeta]
  unfold finiteWiredEventMass
  calc
    (∑ omega,
      (triangularTransShellFullEvent (2 * k) k x).indicator
          (fun _ => (1 : Real)) omega *
        wiredFkProb (triangularTransBoxGraph (2 * k) x)
          (triangularTransBoxBoundary (2 * k) x)
          (1 - Real.exp (-beta)) q omega) =
      ∑ omega,
        (triangularTransShellEvent (2 * k) k x).indicator
            (fun _ => (1 : Real))
            (restrictActive (triangularTransBoxGraph (2 * k) x) omega) *
          wiredFkProb (triangularTransBoxGraph (2 * k) x)
            (triangularTransBoxBoundary (2 * k) x)
            (1 - Real.exp (-beta)) q omega := by
        apply Finset.sum_congr rfl
        intro omega homega
        congr 1
        rw [Set.indicator_apply, Set.indicator_apply]
        have heq := Set.ext_iff.mp
          (restrictActive_preimage_triangularTransShellEvent (2 * k) k x) omega
        split_ifs with h h' <;> simp_all
    _ = _ := htrans

theorem triangularBufferedTransShell_finite_le_theta
    (k : Nat) (hk : 1 ≤ k) (x : Site 2) (m : Nat)
    (hm : triangularTransBufferLevel k x < m)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (triangular.wiredBufferedMeasure m
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (triangularTransBufferLevel k x)
          (triangularBufferedTransShellEvent k x)) ≤
      triangularOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  let L := triangularTransBufferLevel k x
  let incl := triangularTransBoxToBufferedAt k x m hm.le
  have hcomp : ∀ omega : ConfigSpace (Sym2 (triangular.BufferedVertex m)),
      ocd_innerRestrict (triangularTransBoxToBuffered k x)
          (triangular.bufferedRestrictLE hm.le omega) =
        ocd_innerRestrict incl omega := by
    intro omega
    funext e
    have hv : ∀ y : TriangularTransBoxVertex (2 * k) x,
        triangular.bufferedVertexInclLE hm.le
            (triangularTransBoxToBuffered k x y) = incl y := by
      intro y
      rfl
    induction e using Sym2.inductionOn with
    | _ y z =>
        change omega s(triangular.bufferedVertexInclLE hm.le
            (triangularTransBoxToBuffered k x y),
          triangular.bufferedVertexInclLE hm.le
            (triangularTransBoxToBuffered k x z)) =
          omega s(incl y, incl z)
        rw [hv y, hv z]
  have hdom := ocd_wired_inner_dominated_bcProb
    (Gin := triangularTransBoxGraph (2 * k) x)
    (Gout := triangular.bufferedGraph m)
    (ιV := incl)
    (bdryOut := triangular.bufferedBoundary m)
    (triangularTransBoxToBufferedAt_injective k x m hm.le)
    (triangularTransBoxToBufferedAt_adjMatch k x m hm.le)
    (triangularTransBoxBoundary (2 * k) x)
    hp hp1 hq
    (triangularTransBoxToBufferedAt_inducedWiring_le k hk x m hm)
    (triangularTransShellFullEvent_increasing (2 * k) k x)
  rw [triangular.wiredBufferedMeasure_real_cylinder hm.le hp hp1
    (zero_lt_one.trans_le hq) (triangularBufferedTransShellEvent k x)]
  have heventEq :
      triangular.bufferedRestrictLE hm.le ⁻¹'
          triangularBufferedTransShellEvent k x =
        ocd_innerRestrict incl ⁻¹'
          triangularTransShellFullEvent (2 * k) k x := by
    ext omega
    simp only [Set.mem_preimage, triangularBufferedTransShellEvent, hcomp]
  rw [heventEq]
  calc
    (∑ omega,
        (ocd_innerRestrict incl ⁻¹'
          triangularTransShellFullEvent (2 * k) k x).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangular.bufferedGraph m)
            (triangular.bufferedBoundary m) p q omega) ≤
      finiteWiredEventMass (triangularTransBoxGraph (2 * k) x)
        (triangularTransBoxBoundary (2 * k) x) p q
        (triangularTransShellFullEvent (2 * k) k x) := by
      unfold finiteWiredEventMass
      simpa only [bcProb_clique_eq_wiredFkProb] using hdom
    _ = triangularOuterInnerTheta q beta k := by
      simpa [p] using triangularTransFullMass_eq_outerInnerTheta
        k hk x q beta hq hbeta

theorem triangularBufferedTransShell_infinite_le_theta
    (k : Nat) (hk : 1 ≤ k) (x : Site 2) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (triangular.wiredBufferedInfiniteVolume
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (triangularTransBufferLevel k x)
          (triangularBufferedTransShellEvent k x)) ≤
      triangularOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have htend := triangular.wiredBufferedMeasure_tendsto_cylinder
    (triangularTransBufferLevel k x) hp hp1 hq
    (triangularBufferedTransShellEvent_increasing k x)
  apply le_of_tendsto htend
  filter_upwards [eventually_ge_atTop (triangularTransBufferLevel k x + 1)]
    with m hm
  exact triangularBufferedTransShell_finite_le_theta
    k hk x m (by omega) q beta hq hbeta

theorem triangular_twoPointEvent_subset_transShell
    (k : Nat) (hk : 1 ≤ k) (x y : Site 2)
    (hxy : k ≤ centeredRadius x y) :
    triangular.twoPointEvent x y ⊆
      triangular.bufferedCylinder (triangularTransBufferLevel k x)
        (triangularBufferedTransShellEvent k x) := by
  intro omega hconn
  have hxSmall : x ∈ triangularTransBox (k - 1) x := by
    simp [triangularTransBox, StatMech.FK.fvs_transBox]
  have hyOutside : y ∉ triangularTransBox (k - 1) x := by
    intro hy
    have hyrad : centeredRadius x y ≤ k - 1 := by
      rw [centeredRadius, siteRadius_le_iff]
      exact hy
    omega
  obtain ⟨a, haReach, z, haz, hzOutside⟩ :=
    reachable_induce_innerBoundary (triangular.openSubgraph omega)
      (triangularTransBox (k - 1) x) hxSmall hyOutside hconn
  have hazTri : triangularGraph.Adj a.1 z := haz.1
  have hzK : z - x ∈ box 2 k := by
    have hadj := triangular_adj_sub_right x hazTri
    simpa [Nat.sub_add_cancel hk] using
      triangular_adj_mem_box_succ a.2 hadj
  have hzBoundary : z - x ∈ vertexBoundary 2 k := ⟨hzK, hzOutside⟩
  have hz2k : z ∈ triangularTransBox (2 * k) x := by
    exact box_mono 2 (by omega : k ≤ 2 * k) hzK
  let phi : ((triangular.openSubgraph omega).induce
      (triangularTransBox (k - 1) x)) →g
      FK.openSub (triangularTransBoxGraph (2 * k) x)
        (ocd_innerRestrict (triangularTransBoxToBuffered k x)
          (triangular.bufferedRestrict (triangularTransBufferLevel k x) omega)) := {
    toFun := fun a => (⟨a.1, box_mono 2 (by omega : k - 1 ≤ 2 * k) a.2⟩ :
      TriangularTransBoxVertex (2 * k) x)
    map_rel' := by
      intro a b hab
      change triangularGraph.Adj a.1 b.1 ∧ omega s(a.1, b.1) = true at hab
      rw [FK.openSub_adj]
      refine ⟨hab.1, ?_⟩
      simpa [ocd_innerRestrict, ocd_innerEdge, triangularTransBoxToBuffered,
        PeriodicGraph.bufferedRestrict] using hab.2 }
  let zi : TriangularTransBoxVertex (2 * k) x := ⟨z, hz2k⟩
  have hmapped := haReach.map phi
  have hroot : phi ⟨x, hxSmall⟩ = triangularTransBoxCenter (2 * k) x := by
    apply Subtype.ext
    rfl
  have hazInner : (FK.openSub (triangularTransBoxGraph (2 * k) x)
      (ocd_innerRestrict (triangularTransBoxToBuffered k x)
        (triangular.bufferedRestrict (triangularTransBufferLevel k x) omega))).Adj
      (phi a) zi := by
    rw [FK.openSub_adj]
    refine ⟨hazTri, ?_⟩
    simpa [ocd_innerRestrict, ocd_innerEdge, triangularTransBoxToBuffered,
      PeriodicGraph.bufferedRestrict, phi, zi] using haz.2
  have hreachZ := hmapped.trans hazInner.reachable
  have hzShell : zi ∈ triangularTransBoxShell (2 * k) k x := by
    simp only [triangularTransBoxShell, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hzBoundary
  change ocd_innerRestrict (triangularTransBoxToBuffered k x)
      (triangular.bufferedRestrict (triangularTransBufferLevel k x) omega) ∈
    triangularTransShellFullEvent (2 * k) k x
  refine ⟨zi, hzShell, ?_⟩
  rwa [hroot] at hreachZ

theorem triangular_wiredTwoPointProbability_le_theta
    (k : Nat) (hk : 1 ≤ k) (x y : Site 2)
    (hxy : k ≤ centeredRadius x y) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    triangular.wiredTwoPointProbability (1 - Real.exp (-beta)) q x y ≤
      triangularOuterInnerTheta q beta k := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  let mu := triangular.wiredBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq)
  have hmono : (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
      (triangular.twoPointEvent x y) ≤
      (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (triangularTransBufferLevel k x)
          (triangularBufferedTransShellEvent k x)) :=
    measureReal_mono (triangular_twoPointEvent_subset_transShell k hk x y hxy)
      (measure_ne_top _ _)
  rw [show triangular.wiredTwoPointProbability
      (1 - Real.exp (-beta)) q x y =
      (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.twoPointEvent x y) by
    simp [PeriodicGraph.wiredTwoPointProbability, hp, hp1,
      zero_lt_one.trans_le hq, mu]]
  exact hmono.trans
    (triangularBufferedTransShell_infinite_le_theta
      k hk x q beta hq hbeta)

theorem betaOfP_pos {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    0 < -Real.log (1 - p) :=
  neg_pos.mpr (Real.log_neg (sub_pos.mpr hp1) (by linarith))

theorem betaOfP_param {p : Real} (hp1 : p < 1) :
    1 - Real.exp (-(-Real.log (1 - p))) = p := by
  rw [neg_neg, Real.exp_log (sub_pos.mpr hp1)]
  ring

theorem betaOfP_lt_criticalBeta
    (q p : Real) (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hp1 : p < 1) (hsub : p < triangular.criticalPoint q) :
    -Real.log (1 - p) < triangularCriticalBeta q := by
  by_contra hnot
  have hle : triangularCriticalBeta q ≤ -Real.log (1 - p) :=
    le_of_not_gt hnot
  have hexp : Real.exp (-(-Real.log (1 - p))) ≤
      Real.exp (-triangularCriticalBeta q) :=
    Real.exp_le_exp.mpr (neg_le_neg hle)
  have hpEq := betaOfP_param hp1
  have hcEq := triangularCriticalBeta_param q hpc
  linarith

theorem centeredRadius_eq_zero_iff (x y : Site 2) :
    centeredRadius x y = 0 ↔ x = y := by
  constructor
  · intro h
    apply funext
    intro i
    have hle : centeredRadius x y ≤ 0 := h.le
    rw [centeredRadius, siteRadius_le_iff] at hle
    have hi := hle i
    simp only at hi
    have : y i - x i = 0 := Int.natAbs_eq_zero.mp (Nat.le_zero.mp hi)
    linarith
  · rintro rfl
    exact centeredRadius_self x


theorem triangular_subcritical_twoPoint_exponential_decay
    (q : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    SubcriticalTwoPointExponentialDecay
      triangular q (triangular.criticalPoint q) := by
  intro p hp
  have hp1 : p < 1 := hp.2.trans hpc.2
  let beta := -Real.log (1 - p)
  have hbeta : 0 < beta := betaOfP_pos hp.1 hp1
  have hsub : beta < triangularCriticalBeta q :=
    betaOfP_lt_criticalBeta q p hpc hp1 hp.2
  obtain ⟨Q, hQ, hdecay⟩ :=
    triangularOuterInner_exponential_decay_below_critical
      q beta hq hpc hbeta hsub
  let delta := (triangularCriticalBeta q - beta) / 4
  let c := delta / (2 * Q)
  refine ⟨c, 1, ?_, by norm_num, ?_⟩
  · have hdelta : 0 < delta := by dsimp [delta]; linarith
    dsimp [c]
    positivity
  intro x y
  by_cases hxy : x = y
  · subst y
    simpa using triangular.wiredTwoPointProbability_le_one p q x x
  let r := centeredRadius x y
  have hr : 1 ≤ r := by
    exact Nat.one_le_iff_ne_zero.mpr
      (fun h => hxy ((centeredRadius_eq_zero_iff x y).mp h))
  have hpEq : 1 - Real.exp (-beta) = p := by
    dsimp [beta]
    exact betaOfP_param hp1
  have hpoint := triangular_wiredTwoPointProbability_le_theta
    r hr x y le_rfl q beta hq hbeta
  rw [hpEq] at hpoint
  have harm := hdecay r hr
  have hrbox : y - x ∈ box 2 r := by
    rw [mem_box_iff_siteRadius_le]
    change centeredRadius x y ≤ r
    exact le_rfl
  have hdistNat := triangular_dist_le_two_mul_of_sub_mem_box hrbox
  have hdist : (triangularGraph.dist x y : Real) ≤ 2 * (r : Real) := by
    exact_mod_cast hdistNat
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hrate : c * (triangularGraph.dist x y : Real) ≤
      ((r : Real) / Q) * delta := by
    calc
      c * (triangularGraph.dist x y : Real) ≤ c * (2 * (r : Real)) :=
        mul_le_mul_of_nonneg_left hdist hc.le
      _ = ((r : Real) / Q) * delta := by
        dsimp [c]
        field_simp
  calc
    triangular.wiredTwoPointProbability p q x y ≤
        triangularOuterInnerTheta q beta r := hpoint
    _ ≤ Real.exp (-(((r : Real) / Q) * delta)) := by
      simpa [delta, mul_assoc] using harm
    _ ≤ 1 * Real.exp (-c * (triangularGraph.dist x y : Real)) := by
      rw [one_mul]
      simpa [neg_mul] using Real.exp_le_exp.mpr (neg_le_neg hrate)

end StatMech.FK.PeriodicPlanar
