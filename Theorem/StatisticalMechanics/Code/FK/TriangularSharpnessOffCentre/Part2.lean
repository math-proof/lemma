/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
import Def.StatisticalMechanics.Code.FK.TriangularSharpnessOffCentre.Part2
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.RevealmentTranslation

theorem triangularOuterCenteredConn_nonneg
    (n : Nat) (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (x : TriangularBoxVertex n) (j : Nat) :
    0 ≤ triangularOuterCenteredConn n q beta x j := by
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq) omega).le
  unfold triangularOuterCenteredConn
  exact mean_indicator_nonneg hmu0 _

theorem triangularOuterCenteredConn_zero
    (n : Nat) (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (x : TriangularBoxVertex n) :
    triangularOuterCenteredConn n q beta x 0 = 1 := by
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq)
  have hall : (fun omega : ConfigSpace (triangularBoxGraph (2 * n)).edgeSet =>
      if ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n)
        (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
        x (triangularBoxCenteredShell n x 0) then (1 : Real) else 0) =
      fun _ => 1 := by
    funext omega
    rw [if_pos]
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, centeredRadius_self x.1⟩,
      ReachOpen.refl x⟩
  unfold triangularOuterCenteredConn
  rw [hall]
  exact Lindeberg.mean_const mu hmu1 1

theorem triangularOuterCenteredConn_le_one
    (n : Nat) (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (x : TriangularBoxVertex n) (j : Nat) :
    triangularOuterCenteredConn n q beta x j ≤ 1 := by
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq) omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq)
  calc
    triangularOuterCenteredConn n q beta x j ≤
        Lindeberg.mean mu (fun _ => (1 : Real)) := by
      unfold triangularOuterCenteredConn Lindeberg.mean
      apply Finset.sum_le_sum
      intro omega _
      apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
      change (if ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n)
        (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
        x (triangularBoxCenteredShell n x j) then (1 : Real) else 0) ≤ 1
      split_ifs <;> norm_num
    _ = 1 := Lindeberg.mean_const mu hmu1 1

theorem triangularOuterCenteredConn_antitone
    (n : Nat) (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (x : TriangularBoxVertex n) :
    Antitone (triangularOuterCenteredConn n q beta x) := by
  intro j k hjk
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq) omega).le
  unfold triangularOuterCenteredConn
  apply mean_indicator_mono hmu0
  intro omega hconn
  obtain ⟨b, hb, hreach⟩ := hconn
  have hrad : centeredRadius x.1 b.1 = k := (Finset.mem_filter.mp hb).2
  exact triangularBox_reachOpen_hits_centered hreach (hjk.trans_eq hrad.symm)

theorem triangularOuterInnerTheta_nonneg
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) (k : Nat) :
    0 ≤ triangularOuterInnerTheta q beta k := by
  by_cases hk : k = 0
  · simp [triangularOuterInnerTheta, hk]
  rw [triangularOuterInnerTheta, if_neg hk]
  unfold triangularInnerCrossInd Lindeberg.mean
  apply Finset.sum_nonneg
  intro omega _
  apply mul_nonneg
  · change 0 ≤ (openCrossEvent (triangularBoxEndU k) (triangularBoxEndV k)
      (triangularBoxRoot k) (triangularBoxShell k k)).indicator
      (fun _ => (1 : Real))
      (restrictConfig (triangularBoxEdgeLE (by omega : k ≤ 2 * k)) omega)
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  · exact (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq) omega).le

@[simp] theorem triangularOuterInnerTheta_zero (q beta : Real) :
    triangularOuterInnerTheta q beta 0 = 1 := by
  simp [triangularOuterInnerTheta]


theorem triangularCenteredShellEvent_iff_innerCross
    (k : Nat) (hk : 1 ≤ k)
    (omega : ConfigSpace (triangularBoxGraph (2 * k)).edgeSet) :
    omega ∈ triangularCenteredShellEvent (2 * k) k ↔
      restrictConfig (triangularBoxEdgeLE (by omega : k ≤ 2 * k)) omega ∈
        openCrossEvent (triangularBoxEndU k) (triangularBoxEndV k)
          (triangularBoxRoot k) (triangularBoxShell k k) := by
  let incl : TriangularBoxVertex k → TriangularBoxVertex (2 * k) :=
    boxVertInclLE 2 (by omega)
  let iota := triangularBoxEdgeLE (by omega : k ≤ 2 * k)
  constructor
  · rintro ⟨b, hb, hreach⟩
    have hbOuter : b.1 ∉ box 2 (k - 1) := (Finset.mem_filter.mp hb).2.2
    have hroot : (triangularBoxRoot (2 * k)).1 ∈ box 2 (k - 1) := by
      intro j
      simp [triangularBoxRoot]
    have hfirst : ∀ {a b : TriangularBoxVertex (2 * k)},
        ReachOpen (triangularBoxEndU (2 * k)) (triangularBoxEndV (2 * k))
          omega a b →
        ∀ (ha : a.1 ∈ box 2 (k - 1)), b.1 ∉ box 2 (k - 1) →
        ConnOpenSet (triangularBoxEndU k) (triangularBoxEndV k)
          (restrictConfig iota omega)
          ⟨a.1, box_mono 2 (by omega : k - 1 ≤ k) ha⟩
          (triangularBoxShell k k) := by
      intro a b hr
      induction hr with
      | refl a => intro ha hnot; exact (hnot ha).elim
      | @step a y z e hopen hpair hrest ih =>
          intro ha hz
          have hay : (triangularBoxGraph (2 * k)).Adj a y := by
            rcases hpair with hpair | hpair
            · rw [← hpair.1, ← hpair.2]
              exact triangularBox_end_adj (2 * k) e
            · rw [← hpair.1, ← hpair.2]
              exact (triangularBox_end_adj (2 * k) e).symm
          have hak : a.1 ∈ box 2 k := box_mono 2 (by omega) ha
          by_cases hy : y.1 ∈ box 2 (k - 1)
          · obtain ⟨w, hw, hwy⟩ := ih hy hz
            let ai : TriangularBoxVertex k := ⟨a.1, hak⟩
            let yi : TriangularBoxVertex k :=
              ⟨y.1, box_mono 2 (by omega : k - 1 ≤ k) hy⟩
            let ei : (triangularBoxGraph k).edgeSet :=
              ⟨s(ai, yi), by
                rw [SimpleGraph.mem_edgeSet]
                exact hay⟩
            have hei : iota ei = e := by
              apply Subtype.ext
              have hedgeEq : e.1 = s(a, y) := by
                have hout : s(triangularBoxEndU (2 * k) e,
                    triangularBoxEndV (2 * k) e) = e.1 := e.1.out_eq
                rcases hpair with hp | hp
                · simpa [hp.1, hp.2] using hout.symm
                · simpa [hp.1, hp.2, Sym2.eq_swap] using hout.symm
              change innerEdgeLE 2 (by omega : k ≤ 2 * k) ei.1 = e.1
              have hia : boxVertInclLE 2 (by omega : k ≤ 2 * k) ai = a :=
                Subtype.ext (by rfl)
              have hiy : boxVertInclLE 2 (by omega : k ≤ 2 * k) yi = y :=
                Subtype.ext (by rfl)
              rw [show ei.1 = s(ai, yi) from rfl, innerEdgeLE, Sym2.map_mk,
                hia, hiy, ← hedgeEq]
            have heiOpen : restrictConfig iota omega ei = true := by
              change omega (iota ei) = true
              rw [hei]
              exact hopen
            have heEnds :
                ((triangularBoxEndU k ei = ai ∧ triangularBoxEndV k ei = yi) ∨
                 (triangularBoxEndU k ei = yi ∧ triangularBoxEndV k ei = ai)) := by
              have hout := ei.1.out_eq
              change s(triangularBoxEndU k ei, triangularBoxEndV k ei) =
                s(ai, yi) at hout
              exact Sym2.eq_iff.mp hout
            have htail : ReachOpen (triangularBoxEndU k) (triangularBoxEndV k)
                (restrictConfig iota omega) yi w := by
              simpa [yi] using hwy
            refine ⟨w, hw, ?_⟩
            simpa [ai] using ReachOpen.step ei heiOpen heEnds htail
          · have hyk : y.1 ∈ box 2 k :=
              triangular_adj_mem_box_of_mem_pred hk ha hay
            let ai : TriangularBoxVertex k := ⟨a.1, hak⟩
            let yi : TriangularBoxVertex k := ⟨y.1, hyk⟩
            let ei : (triangularBoxGraph k).edgeSet :=
              ⟨s(ai, yi), by rw [SimpleGraph.mem_edgeSet]; exact hay⟩
            have hei : iota ei = e := by
              apply Subtype.ext
              have hedgeEq : e.1 = s(a, y) := by
                have hout : s(triangularBoxEndU (2 * k) e,
                    triangularBoxEndV (2 * k) e) = e.1 := e.1.out_eq
                rcases hpair with hp | hp
                · simpa [hp.1, hp.2] using hout.symm
                · simpa [hp.1, hp.2, Sym2.eq_swap] using hout.symm
              change innerEdgeLE 2 (by omega : k ≤ 2 * k) ei.1 = e.1
              have hia : boxVertInclLE 2 (by omega : k ≤ 2 * k) ai = a :=
                Subtype.ext (by rfl)
              have hiy : boxVertInclLE 2 (by omega : k ≤ 2 * k) yi = y :=
                Subtype.ext (by rfl)
              rw [show ei.1 = s(ai, yi) from rfl, innerEdgeLE, Sym2.map_mk,
                hia, hiy, ← hedgeEq]
            have heiOpen : restrictConfig iota omega ei = true := by
              change omega (iota ei) = true
              rw [hei]
              exact hopen
            have heEnds :
                ((triangularBoxEndU k ei = ai ∧ triangularBoxEndV k ei = yi) ∨
                 (triangularBoxEndU k ei = yi ∧ triangularBoxEndV k ei = ai)) := by
              have hout := ei.1.out_eq
              change s(triangularBoxEndU k ei, triangularBoxEndV k ei) =
                s(ai, yi) at hout
              exact Sym2.eq_iff.mp hout
            refine ⟨yi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyk, hy⟩, ?_⟩
            simpa [ai] using ReachOpen.step ei heiOpen heEnds (ReachOpen.refl yi)
    simpa [incl, iota, triangularBoxRoot] using hfirst hreach hroot hbOuter
  · rintro ⟨b, hb, hreach⟩
    have hlift : ∀ {a b : TriangularBoxVertex k},
        ReachOpen (triangularBoxEndU k) (triangularBoxEndV k)
          (restrictConfig iota omega) a b →
        ReachOpen (triangularBoxEndU (2 * k)) (triangularBoxEndV (2 * k))
          omega (incl a) (incl b) := by
      intro a b hr
      induction hr with
      | refl a => exact ReachOpen.refl (incl a)
      | @step a y z e hopen hpair hrest ih =>
          let eo := iota e
          have heoOpen : omega eo = true := hopen
          have hepairInner : e.1 = s(a, y) := by
            have hout : s(triangularBoxEndU k e, triangularBoxEndV k e) = e.1 :=
              e.1.out_eq
            rcases hpair with hp | hp
            · simpa [hp.1, hp.2] using hout.symm
            · simpa [hp.1, hp.2, Sym2.eq_swap] using hout.symm
          have heoPair : eo.1 = s(incl a, incl y) := by
            change innerEdgeLE 2 (by omega : k ≤ 2 * k) e.1 =
              s(incl a, incl y)
            rw [innerEdgeLE, hepairInner, Sym2.map_mk]
          have heEnds :
              ((triangularBoxEndU (2 * k) eo = incl a ∧
                triangularBoxEndV (2 * k) eo = incl y) ∨
               (triangularBoxEndU (2 * k) eo = incl y ∧
                triangularBoxEndV (2 * k) eo = incl a)) := by
            have hout : s(triangularBoxEndU (2 * k) eo,
                triangularBoxEndV (2 * k) eo) = eo.1 := eo.1.out_eq
            rw [heoPair] at hout
            exact Sym2.eq_iff.mp hout
          exact ReachOpen.step eo heoOpen heEnds ih
    refine ⟨incl b, ?_, hlift hreach⟩
    have hb' := (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'.1,
      fun hsmall => hb'.2 hsmall⟩

theorem triangularCenteredFullMass_eq_outerInnerTheta
    (k : Nat) (hk : 1 ≤ k) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (∑ omega : ConfigSpace (Sym2 (TriangularBoxVertex (2 * k))),
        (triangularCenteredShellFullEvent (2 * k) k).indicator
            (fun _ => (1 : Real)) omega *
          FK.wiredFkProb (triangularBoxGraph (2 * k))
            (fun y => y ∈ triangularBoxShell (2 * k) (2 * k))
            (1 - Real.exp (-beta)) q omega) =
      triangularOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  let G := triangularBoxGraph (2 * k)
  let boundary : TriangularBoxVertex (2 * k) → Prop :=
    fun y => y ∈ triangularBoxShell (2 * k) (2 * k)
  let A := triangularCenteredShellEvent (2 * k) k
  have hparam : FK.betaParams
      (fun _ : Sym2 (TriangularBoxVertex (2 * k)) => (1 : Real)) beta =
      fun _ => p := by
    funext e
    simp [FK.betaParams, p]
  have hmean := FK.activeBCMean_boundaryClique_eq_wired
    G boundary hp hp1 hq0 (A.indicator fun _ => (1 : Real))
  have hevent : triangularInnerCrossInd k =
      A.indicator (fun _ => (1 : Real)) := by
    funext omega
    unfold triangularInnerCrossInd
    rw [Set.indicator_apply, Set.indicator_apply]
    have hiff := triangularCenteredShellEvent_iff_innerCross k hk omega
    by_cases h : omega ∈ A
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hi => h (hiff.mpr hi))]
  have hactive :
      FK.activeBCMean G (boundaryCliqueGraph boundary) (fun _ => p) q
          (A.indicator fun _ => (1 : Real)) =
        triangularOuterInnerTheta q beta k := by
    have hk0 : k ≠ 0 := by omega
    rw [triangularOuterInnerTheta, if_neg hk0, ← hevent, hparam]
    rfl
  rw [← hactive]
  rw [hmean]
  apply Finset.sum_congr rfl
  intro omega _
  have hpre := restrictActive_preimage_triangularCenteredShellEvent (2 * k) k
  have hiff : restrictActive G omega ∈ A ↔
      omega ∈ triangularCenteredShellFullEvent (2 * k) k := by
    rw [← Set.mem_preimage]
    exact Set.ext_iff.mp hpre omega
  by_cases h : restrictActive G omega ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun hf => h (hiff.mpr hf))]

theorem triangular_centeredConn_imp_transShell
    {n k : Nat} (x : TriangularBoxVertex n) (hk : 1 ≤ k)
    (hkn : 2 * k < n)
    (rho : ConfigSpace (triangularBoxGraph (2 * n)).edgeSet)
    (hconn : ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n)
      (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) rho)
      x (triangularBoxCenteredShell n x k)) :
    let hsub := triangularTransBox_subset_double x.2 hkn
    let transIncl := triangularTransBoxIncl hsub
    let hadjm := ocd_comapAdjMatch triangularGraph transIncl (fun _ => rfl)
    ocd_innerRestrictActive (triangularTransBoxGraph (2 * k) x.1)
        (triangularBoxGraph (2 * n)) transIncl hadjm rho ∈
      triangularTransShellEvent (2 * k) k x.1 := by
  let hsub := triangularTransBox_subset_double x.2 hkn
  let transIncl := triangularTransBoxIncl hsub
  let hadjm := ocd_comapAdjMatch triangularGraph transIncl (fun _ => rfl)
  let transCfg := ocd_innerRestrictActive
    (triangularTransBoxGraph (2 * k) x.1)
    (triangularBoxGraph (2 * n)) transIncl hadjm rho
  let iotaN := triangularBoxEdgeLE (by omega : n ≤ 2 * n)
  obtain ⟨b, hb, hreach⟩ := hconn
  have hbRad : centeredRadius x.1 b.1 = k := (Finset.mem_filter.mp hb).2
  have hbOuter : b.1 - x.1 ∉ box 2 (k - 1) := by
    intro hbIn
    have hbLe : centeredRadius x.1 b.1 ≤ k - 1 := by
      have := mem_box_iff_siteRadius_le.mp hbIn
      change siteRadius (fun i => b.1 i - x.1 i) ≤ k - 1
      simpa only [Pi.sub_apply] using this
    omega
  have hxInner : x.1 - x.1 ∈ box 2 (k - 1) := by simp
  have hfirst : ∀ {a b : TriangularBoxVertex n},
      ReachOpen (triangularBoxEndU n) (triangularBoxEndV n)
        (restrictConfig iotaN rho) a b →
      ∀ (ha : a.1 - x.1 ∈ box 2 (k - 1)),
        b.1 - x.1 ∉ box 2 (k - 1) →
      ConnOpenSet (triangularTransBoxEndU (2 * k) x.1)
        (triangularTransBoxEndV (2 * k) x.1) transCfg
        ⟨a.1, by
          apply box_mono 2 (by omega : k - 1 ≤ 2 * k)
          exact ha⟩
        (triangularTransBoxShell (2 * k) k x.1) := by
    intro a b hr
    induction hr with
    | refl a => intro ha hnot; exact (hnot ha).elim
    | @step a y z e hopen hpair hrest ih =>
        intro ha hz
        have hay : (triangularBoxGraph n).Adj a y := by
          rcases hpair with hp | hp
          · rw [← hp.1, ← hp.2]
            exact triangularBox_end_adj n e
          · rw [← hp.1, ← hp.2]
            exact (triangularBox_end_adj n e).symm
        have hadjSub : triangularGraph.Adj (a.1 - x.1) (y.1 - x.1) :=
          triangular_adj_sub_right x.1 hay
        have hak : a.1 - x.1 ∈ box 2 k := box_mono 2 (by omega) ha
        by_cases hy : y.1 - x.1 ∈ box 2 (k - 1)
        · obtain ⟨w, hw, hwy⟩ := ih hy hz
          let av : TriangularTransBoxVertex (2 * k) x.1 :=
            ⟨a.1, box_mono 2 (by omega : k ≤ 2 * k) hak⟩
          have hyk : y.1 - x.1 ∈ box 2 k := box_mono 2 (by omega) hy
          let yt : TriangularTransBoxVertex (2 * k) x.1 :=
            ⟨y.1, box_mono 2 (by omega : k ≤ 2 * k) hyk⟩
          let et : (triangularTransBoxGraph (2 * k) x.1).edgeSet :=
            ⟨s(av, yt), by rw [SimpleGraph.mem_edgeSet]; exact hay⟩
          let etOut : (triangularBoxGraph (2 * n)).edgeSet :=
            ⟨ocd_innerEdge transIncl et.1, by
              unfold ocd_innerEdge
              rw [show et.1 = s(av, yt) from rfl, Sym2.map_mk,
                SimpleGraph.mem_edgeSet]
              change triangularGraph.Adj (transIncl av).1 (transIncl yt).1
              exact hay⟩
          have hedgeSource : e.1 = s(a, y) := by
            have hout : s(triangularBoxEndU n e, triangularBoxEndV n e) = e.1 :=
              e.1.out_eq
            rcases hpair with hp | hp
            · simpa [hp.1, hp.2] using hout.symm
            · simpa [hp.1, hp.2, Sym2.eq_swap] using hout.symm
          have houtEq : etOut = iotaN e := by
            apply Subtype.ext
            change Sym2.map transIncl et.1 = innerEdgeLE 2 (by omega) e.1
            have hta : transIncl av = boxVertInclLE 2
                (by omega : n ≤ 2 * n) a := Subtype.ext (by rfl)
            have hty : transIncl yt = boxVertInclLE 2
                (by omega : n ≤ 2 * n) y := Subtype.ext (by rfl)
            rw [show et.1 = s(av, yt) from rfl,
              Sym2.map_mk, innerEdgeLE, hedgeSource, Sym2.map_mk, hta, hty]
          have etOpen : transCfg et = true := by
            change rho etOut = true
            rw [houtEq]
            exact hopen
          have etEnds :
              ((triangularTransBoxEndU (2 * k) x.1 et = av ∧
                triangularTransBoxEndV (2 * k) x.1 et = yt) ∨
               (triangularTransBoxEndU (2 * k) x.1 et = yt ∧
                triangularTransBoxEndV (2 * k) x.1 et = av)) := by
            have hout := et.1.out_eq
            change s(triangularTransBoxEndU (2 * k) x.1 et,
              triangularTransBoxEndV (2 * k) x.1 et) = s(av, yt) at hout
            exact Sym2.eq_iff.mp hout
          have htail : ReachOpen (triangularTransBoxEndU (2 * k) x.1)
              (triangularTransBoxEndV (2 * k) x.1) transCfg yt w := by
            simpa [yt] using hwy
          refine ⟨w, hw, ?_⟩
          simpa [av] using ReachOpen.step et etOpen etEnds htail
        · have hyk : y.1 - x.1 ∈ box 2 k :=
            triangular_adj_mem_box_of_mem_pred hk ha hadjSub
          let av : TriangularTransBoxVertex (2 * k) x.1 :=
            ⟨a.1, box_mono 2 (by omega : k ≤ 2 * k) hak⟩
          let yt : TriangularTransBoxVertex (2 * k) x.1 :=
            ⟨y.1, box_mono 2 (by omega : k ≤ 2 * k) hyk⟩
          let et : (triangularTransBoxGraph (2 * k) x.1).edgeSet :=
            ⟨s(av, yt), by rw [SimpleGraph.mem_edgeSet]; exact hay⟩
          let etOut : (triangularBoxGraph (2 * n)).edgeSet :=
            ⟨ocd_innerEdge transIncl et.1, by
              unfold ocd_innerEdge
              rw [show et.1 = s(av, yt) from rfl, Sym2.map_mk,
                SimpleGraph.mem_edgeSet]
              change triangularGraph.Adj (transIncl av).1 (transIncl yt).1
              exact hay⟩
          have hedgeSource : e.1 = s(a, y) := by
            have hout : s(triangularBoxEndU n e, triangularBoxEndV n e) = e.1 :=
              e.1.out_eq
            rcases hpair with hp | hp
            · simpa [hp.1, hp.2] using hout.symm
            · simpa [hp.1, hp.2, Sym2.eq_swap] using hout.symm
          have houtEq : etOut = iotaN e := by
            apply Subtype.ext
            change Sym2.map transIncl et.1 = innerEdgeLE 2 (by omega) e.1
            have hta : transIncl av = boxVertInclLE 2
                (by omega : n ≤ 2 * n) a := Subtype.ext (by rfl)
            have hty : transIncl yt = boxVertInclLE 2
                (by omega : n ≤ 2 * n) y := Subtype.ext (by rfl)
            rw [show et.1 = s(av, yt) from rfl,
              Sym2.map_mk, innerEdgeLE, hedgeSource, Sym2.map_mk, hta, hty]
          have etOpen : transCfg et = true := by
            change rho etOut = true
            rw [houtEq]
            exact hopen
          have etEnds :
              ((triangularTransBoxEndU (2 * k) x.1 et = av ∧
                triangularTransBoxEndV (2 * k) x.1 et = yt) ∨
               (triangularTransBoxEndU (2 * k) x.1 et = yt ∧
                triangularTransBoxEndV (2 * k) x.1 et = av)) := by
            have hout := et.1.out_eq
            change s(triangularTransBoxEndU (2 * k) x.1 et,
              triangularTransBoxEndV (2 * k) x.1 et) = s(av, yt) at hout
            exact Sym2.eq_iff.mp hout
          have etMem : yt ∈ triangularTransBoxShell (2 * k) k x.1 := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyk, ?_⟩
            intro hsmall
            exact hy hsmall
          refine ⟨yt, etMem, ?_⟩
          simpa [av] using ReachOpen.step et etOpen etEnds (ReachOpen.refl yt)
  have hresult := hfirst hreach hxInner hbOuter
  simpa [transCfg, transIncl, hsub, hadjm, iotaN,
    triangularTransShellEvent, triangularTransBoxCenter] using hresult

theorem triangularOuterCenteredConn_le_theta_strict
    (n k : Nat) (x : TriangularBoxVertex n)
    (hk : 1 ≤ k) (hkn : 2 * k < n)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    triangularOuterCenteredConn n q beta x k ≤
      triangularOuterInnerTheta q beta k := by
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let hsub := triangularTransBox_subset_double x.2 hkn
  let transIncl := triangularTransBoxIncl hsub
  let hadjm := ocd_comapAdjMatch triangularGraph transIncl (fun _ => rfl)
  let A := triangularTransShellEvent (2 * k) k x.1
  let obs : ConfigSpace (triangularBoxGraph (2 * n)).edgeSet → Real := fun rho =>
    A.indicator (fun _ => (1 : Real))
      (ocd_innerRestrictActive (triangularTransBoxGraph (2 * k) x.1)
        (triangularBoxGraph (2 * n)) transIncl hadjm rho)
  have hmu0 : ∀ rho, 0 ≤ mu rho := fun rho =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq) rho).le
  have hleft : triangularOuterCenteredConn n q beta x k ≤
      Lindeberg.mean mu obs := by
    unfold triangularOuterCenteredConn
    apply mean_indicator_mono hmu0
    intro rho hconn
    exact triangular_centeredConn_imp_transShell x hk hkn rho hconn
  have hdom := triangularTransBox_activeBCMean_le x.2 hk hkn q beta hq hbeta
    (triangularTransShellEvent_increasing (2 * k) k x.1)
  have htrans := triangularTransShellEvent_betaMean_eq_centeredFullMass
    (2 * k) k x.1 q beta (zero_lt_one.trans_le hq) hbeta
  have hcenter := triangularCenteredFullMass_eq_outerInnerTheta
    k hk q beta hq hbeta
  calc
    triangularOuterCenteredConn n q beta x k ≤ Lindeberg.mean mu obs := hleft
    _ ≤ FK.activeBCMean (triangularTransBoxGraph (2 * k) x.1)
        (boundaryCliqueGraph (triangularTransBoxBoundary (2 * k) x.1))
        (FK.betaParams (fun _ => 1) beta) q
        (A.indicator fun _ => (1 : Real)) := by
      simpa [mu, obs, A, transIncl, hsub, hadjm,
        triangularBoxBoundaryGraph] using hdom
    _ = triangularOuterInnerTheta q beta k := by
      rw [show FK.activeBCMean (triangularTransBoxGraph (2 * k) x.1)
          (boundaryCliqueGraph (triangularTransBoxBoundary (2 * k) x.1))
          (FK.betaParams (fun _ => 1) beta) q
          (A.indicator fun _ => (1 : Real)) =
          ∑ omega : ConfigSpace (Sym2 (TriangularBoxVertex (2 * k))),
            (triangularCenteredShellFullEvent (2 * k) k).indicator
                (fun _ => (1 : Real)) omega *
              FK.wiredFkProb (triangularBoxGraph (2 * k))
                (fun y => y ∈ triangularBoxShell (2 * k) (2 * k))
                (1 - Real.exp (-beta)) q omega by
        simpa [A] using htrans]
      exact hcenter

theorem triangularCenteredDenom_pos
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    0 < triangularCenteredDenom n q beta := by
  let M := (Finset.univ : Finset (TriangularBoxVertex n)).sup'
    ⟨triangularBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ j ∈ Finset.range n,
      triangularOuterCenteredConn n q beta x j)
  have hsum : 1 ≤ ∑ j ∈ Finset.range n,
      triangularOuterCenteredConn n q beta (triangularBoxRoot n) j := by
    rw [← triangularOuterCenteredConn_zero n q beta hq hbeta
      (triangularBoxRoot n)]
    apply Finset.single_le_sum
      (fun j _ => triangularOuterCenteredConn_nonneg n q beta hq hbeta _ j)
    simpa using hn
  have hsup := Finset.le_sup'
    (fun x => ∑ j ∈ Finset.range n,
      triangularOuterCenteredConn n q beta x j)
    (Finset.mem_univ (triangularBoxRoot n))
  have hM : 0 < M := by change _ ≤ M at hsup; linarith
  have hnR : 0 < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  unfold triangularCenteredDenom
  change 0 < 4 * M / (n : Real)
  positivity


theorem triangular_outer_inner_hcov_centered
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
      (triangularBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (triangularInnerCrossInd n) *
        (1 - Lindeberg.mean mu (triangularInnerCrossInd n)) /
          triangularCenteredDenom n q beta ≤
      ∑ e, Lindeberg.cov mu (triangularInnerCrossInd n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (TriangularBoxVertex n)).sup'
    ⟨triangularBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ j ∈ Finset.range n,
      triangularOuterCenteredConn n q beta x j)
  let D := 4 * M / (n : Real)
  have hD : 0 < D := by
    simpa [triangularCenteredDenom, M, D] using
      triangularCenteredDenom_pos n hn q beta hq hbeta
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta)
      (zero_lt_one.trans_le hq) omega).le
  have hsum : ∀ e : (triangularBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean mu (fun omega => if ConnOpenSet
          (triangularBoxEndU n) (triangularBoxEndV n)
          (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
          (triangularBoxEndU n e) (triangularBoxShell n k)
          then (1 : Real) else 0) +
        Lindeberg.mean mu (fun omega => if ConnOpenSet
          (triangularBoxEndU n) (triangularBoxEndV n)
          (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
          (triangularBoxEndV n e) (triangularBoxShell n k)
          then (1 : Real) else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
    intro e
    have hu := triangular_rootShell_sum_le_centered_sup n mu hmu0
      (triangularBoxEndU n e)
    have hv := triangular_rootShell_sum_le_centered_sup n mu hmu0
      (triangularBoxEndV n e)
    change _ ≤ 2 * M at hu hv
    have hcard : (Fintype.card (↑(Finset.Icc 1 n)) : Real) = n := by
      rw [Fintype.card_coe, Nat.card_Icc]
      norm_num
    rw [Finset.sum_add_distrib, hcard]
    change _ ≤ (n : Real) * (4 * M / (n : Real))
    have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    rw [mul_div_cancel₀ _ hnR.ne']
    linarith
  have hmain := triangular_outer_inner_hcov n hn q beta D hq hbeta hD
    (by simpa [mu] using hsum)
  simpa [triangularCenteredDenom, mu, M, D] using hmain


theorem triangular_centered_sup_le_two_sig_of_strict_comparison
    (n : Nat) (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hcomp : ∀ x : TriangularBoxVertex n, ∀ k,
      k ∈ Finset.Icc 1 (n / 2) → 2 * k < n →
      triangularOuterCenteredConn n q beta x k ≤
        triangularOuterInnerTheta q beta k) :
    (Finset.univ : Finset (TriangularBoxVertex n)).sup'
        ⟨triangularBoxRoot n, Finset.mem_univ _⟩
        (fun x => ∑ j ∈ Finset.range n,
          triangularOuterCenteredConn n q beta x j) ≤
      2 * triangularOuterInnerSig n q beta := by
  apply Finset.sup'_le
  intro x hx
  exact StatMech.OSSS.antitone_sum_range_le_two_profile_strict
    (triangularOuterCenteredConn n q beta x)
    (triangularOuterInnerTheta q beta)
    (triangularOuterCenteredConn_nonneg n q beta hq hbeta x)
    (triangularOuterCenteredConn_antitone n q beta hq hbeta x)
    (triangularOuterInnerTheta_nonneg q beta hq hbeta) n
    (by rw [triangularOuterCenteredConn_zero n q beta hq hbeta x,
      triangularOuterInnerTheta_zero])
    (fun k hk hstrict => hcomp x k hk hstrict)
    (fun k hk => by
      rw [triangularOuterInnerTheta_zero]
      exact triangularOuterCenteredConn_le_one n q beta hq hbeta x k)

theorem triangularCenteredDenom_le_eight_sig_of_strict_comparison
    (n : Nat) (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hcomp : ∀ x : TriangularBoxVertex n, ∀ k,
      k ∈ Finset.Icc 1 (n / 2) → 2 * k < n →
      triangularOuterCenteredConn n q beta x k ≤
        triangularOuterInnerTheta q beta k) :
    triangularCenteredDenom n q beta ≤
      8 * triangularOuterInnerSig n q beta / (n : Real) := by
  have hsup := triangular_centered_sup_le_two_sig_of_strict_comparison
    n q beta hq hbeta hcomp
  unfold triangularCenteredDenom
  calc
    4 * (Finset.univ : Finset (TriangularBoxVertex n)).sup'
          ⟨triangularBoxRoot n, Finset.mem_univ _⟩
          (fun x => ∑ j ∈ Finset.range n,
            triangularOuterCenteredConn n q beta x j) / (n : Real) ≤
        4 * (2 * triangularOuterInnerSig n q beta) / (n : Real) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsup (by norm_num)) (Nat.cast_nonneg n)
    _ = 8 * triangularOuterInnerSig n q beta / (n : Real) := by ring

theorem triangular_outer_inner_hcov_sharp_of_strict_comparison
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hcomp : ∀ x : TriangularBoxVertex n, ∀ k,
      k ∈ Finset.Icc 1 (n / 2) → 2 * k < n →
      triangularOuterCenteredConn n q beta x k ≤
        triangularOuterInnerTheta q beta k) :
    let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
      (triangularBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (triangularInnerCrossInd n) *
        (1 - Lindeberg.mean mu (triangularInnerCrossInd n)) /
          (8 * triangularOuterInnerSig n q beta / (n : Real)) ≤
      ∑ e, Lindeberg.cov mu (triangularInnerCrossInd n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let theta := Lindeberg.mean mu (triangularInnerCrossInd n)
  have htheta0 : 0 ≤ theta := by
    unfold theta triangularInnerCrossInd Lindeberg.mean
    exact Finset.sum_nonneg fun omega _ => mul_nonneg (by
      change 0 ≤ (openCrossEvent (triangularBoxEndU n) (triangularBoxEndV n)
        (triangularBoxRoot n) (triangularBoxShell n n)).indicator
        (fun _ => (1 : Real))
        (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
      rw [Set.indicator_apply]
      split_ifs <;> norm_num) (FK.activeBCProb_pos _ _
        (FK.betaParams_pos (fun _ => by norm_num) hbeta)
        (FK.betaParams_lt_one (fun _ => 1) beta)
        (zero_lt_one.trans_le hq) omega).le
  have htheta1 : theta ≤ 1 := by
    let mu1 := FK.activeBCProb (triangularBoxGraph (2 * n))
      (triangularBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    have hmu0 : ∀ omega, 0 ≤ mu1 omega := fun omega =>
      (FK.activeBCProb_pos _ _
        (FK.betaParams_pos (fun _ => by norm_num) hbeta)
        (FK.betaParams_lt_one (fun _ => 1) beta)
        (zero_lt_one.trans_le hq) omega).le
    have hmu1 : ∑ omega, mu1 omega = 1 :=
      FK.activeBCProb_sum_eq_one _ _
        (FK.betaParams_pos (fun _ => by norm_num) hbeta)
        (FK.betaParams_lt_one (fun _ => 1) beta)
        (zero_lt_one.trans_le hq)
    calc
      theta ≤ Lindeberg.mean mu1 (fun _ => (1 : Real)) := by
        unfold theta triangularInnerCrossInd Lindeberg.mean mu mu1
        apply Finset.sum_le_sum
        intro omega _
        apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
        change (openCrossEvent (triangularBoxEndU n) (triangularBoxEndV n)
          (triangularBoxRoot n) (triangularBoxShell n n)).indicator
          (fun _ => (1 : Real))
          (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega) ≤ 1
        rw [Set.indicator_apply]
        split_ifs <;> norm_num
      _ = 1 := Lindeberg.mean_const mu1 hmu1 1
  have hnum : 0 ≤ theta * (1 - theta) :=
    mul_nonneg htheta0 (sub_nonneg.mpr htheta1)
  have hDpos := triangularCenteredDenom_pos n hn q beta hq hbeta
  have hDle := triangularCenteredDenom_le_eight_sig_of_strict_comparison
    n q beta hq hbeta hcomp
  have hfrac : theta * (1 - theta) /
      (8 * triangularOuterInnerSig n q beta / (n : Real)) ≤
      theta * (1 - theta) / triangularCenteredDenom n q beta :=
    div_le_div_of_nonneg_left hnum hDpos hDle
  have hbase := triangular_outer_inner_hcov_centered n hn q beta hq hbeta
  exact hfrac.trans (by simpa [mu, theta] using hbase)

theorem triangular_outer_inner_differential_sharp_of_strict_comparison
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hcomp : ∀ x : TriangularBoxVertex n, ∀ k,
      k ∈ Finset.Icc 1 (n / 2) → 2 * k < n →
      triangularOuterCenteredConn n q beta x k ≤
        triangularOuterInnerTheta q beta k) :
    triangularOuterInnerTheta q beta n *
        (1 - triangularOuterInnerTheta q beta n) /
          (8 * triangularOuterInnerSig n q beta / (n : Real)) ≤
      triangularOuterInnerThetaPrime n q beta := by
  letI : Nonempty (triangularBoxGraph (2 * n)).edgeSet :=
    triangularBoxGraph_edgeSet_nonempty (2 * n) (by omega)
  let G := triangularBoxGraph (2 * n)
  let C := triangularBoxBoundaryGraph (2 * n)
  let J : Sym2 (TriangularBoxVertex (2 * n)) → Real := fun _ => 1
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  let f := triangularInnerCrossInd n
  have hJ : ∀ e, 0 < J e := fun _ => by simp [J]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hcov : Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) /
        (8 * triangularOuterInnerSig n q beta / (n : Real)) ≤
      ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
    simpa [G, C, J, mu, f] using
      triangular_outer_inner_hcov_sharp_of_strict_comparison
        n hn q beta hq hbeta hcomp
  have hpos : ∀ omega, 0 < mu omega :=
    FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    FK.activeBCProb_FKGLatticeCondition G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq
  have hf : Monotone f := triangularInnerCrossInd_monotone n
  have hcov0 : ∀ e : G.edgeSet,
      0 ≤ FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e) := by
    intro e
    rw [← StatMech.OSSS.ActiveBoundaryDifferential.cov_activeBC_eq]
    exact LindebergTree.cov_coord_nonneg hpos hmu1 hFKG hf e
  have hderiv := FK.hasDerivAt_activeBCMean_beta_sum G C hJ hbeta hq0 f
  have hderivEq :
      deriv (fun b => FK.activeBCMean G C (FK.betaParams J b) q f) beta =
        ∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(beta * J e.1)))) *
          FK.activeBCCov G C (FK.betaParams J beta) q f
            (Lindeberg.coord e) := by
    rw [hderiv.deriv]
    simp only [FK.betaParams]
  have hpref : ∀ e : G.edgeSet,
      (1 : Real) ≤ J e.1 / (1 - Real.exp (-(beta * J e.1))) := by
    intro e
    have hden : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    simp only [J, mul_one]
    rw [le_div_iff₀ hden]
    linarith [Real.exp_pos (-beta)]
  have hRusso : ∑ e : G.edgeSet,
      FK.activeBCCov G C (FK.betaParams J beta) q f (Lindeberg.coord e) ≤
      deriv (fun b => FK.activeBCMean G C (FK.betaParams J b) q f) beta := by
    rw [hderivEq]
    simpa using StatMech.OSSS.RussoPrefactor.rp_prefactor_extraction
      (fun e : G.edgeSet => J e.1 / (1 - Real.exp (-(beta * J e.1))))
      (fun e => FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e)) 1 hpref hcov0
  have hmain := hcov.trans (by
    simpa [StatMech.OSSS.ActiveBoundaryDifferential.cov_activeBC_eq] using hRusso)
  have hn0 : n ≠ 0 := by omega
  simpa [triangularOuterInnerTheta, triangularOuterInnerThetaPrime,
    hn0, G, C, J, mu, f] using hmain

end StatMech.FK.PeriodicPlanar
