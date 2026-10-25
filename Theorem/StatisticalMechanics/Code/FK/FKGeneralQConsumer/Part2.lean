/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.fkc_rqvanhove.Part4
import Theorem.StatisticalMechanics.Code.FK.FKUniqPerEdge.Part3
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Def.StatisticalMechanics.Code.FK.FKGeneralQConsumer
open scoped BigOperators
open MeasureTheory Filter Topology SimpleGraph Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000


namespace StatMech.FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}


theorem fkgq_avgDensity_eq_sum_edgeMarg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q s : ℝ) :
    fkgq_avgDensity G q s = (1 / (G.edgeFinset.card : ℝ)) *
      ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G (fsc_logistic s) q) e := by
  unfold fkgq_avgDensity fkExpect
  rw [show (fun ω => fkProb G (fsc_logistic s) q ω * (openCount G ω : ℝ)) =
      fun ω => dfi_openEdgeCount G.edgeFinset ω * fkProb G (fsc_logistic s) q ω from ?_]
  · rw [dfi_openEdgeCount_expect]
  · funext ω
    rw [adc_openCount_eq_sum]
    ring


theorem fkgq_freeBulkCollapse_n1 (q s : ℝ) (hq : 0 < q)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (nhds 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic s) q) e - L| ≤ δ n)
    (hbdy : Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) /
          (boxGraph d n).edgeFinset.card) atTop (nhds 0)) :
    Tendsto (fun n => fkgq_avgDensity (boxGraph d n) q s) atTop (nhds L) := by
  rw [← tendsto_add_atTop_iff_nat
    (f := fun n => fkgq_avgDensity (boxGraph d n) q s) 1]
  have hrepr : (fun n => fkgq_avgDensity (boxGraph d (n + 1)) q s) = fun n =>
      (1 / ((boxGraph d (n + 1)).edgeFinset.card : ℝ)) *
        ∑ e ∈ (boxGraph d (n + 1)).edgeFinset,
          edgeMargProb (fkProb (boxGraph d (n + 1)) (fsc_logistic s) q) e := by
    funext n
    exact fkgq_avgDensity_eq_sum_edgeMarg (boxGraph d (n + 1)) q s
  rw [hrepr]
  exact adc_absavg_tendsto
    (ι := fun n => Sym2 (boxVerts d (n + 1)))
    (En := fun n => (boxGraph d (n + 1)).edgeFinset) (fun n => In (n + 1))
    (fn := fun n e => edgeMargProb
      (fkProb (boxGraph d (n + 1)) (fsc_logistic s) q) e)
    L (fun n => δ (n + 1)) (fun n => hIE (n + 1))
    (fun n e _ => adc_edgeMargProb_fkProb_nonneg (boxGraph d (n + 1))
      (fsc_logistic_pos s) (fsc_logistic_lt_one s) hq e)
    (fun n e _ => adc_edgeMargProb_fkProb_le_one (boxGraph d (n + 1))
      (fsc_logistic_pos s) (fsc_logistic_lt_one s) hq e)
    hL0 hL1 (fun n => hδ0 (n + 1)) (hδlim.comp (tendsto_add_atTop_nat 1))
    (fun n => hin (n + 1)) (fun n => hbox1 (n + 1) (by omega))
    (hbdy.comp (tendsto_add_atTop_nat 1))


theorem fkgq_wiredBulkCollapse_n1 (q s : ℝ) (hq : 0 < q)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (nhds 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n)
          (fsc_logistic s) q) e - L| ≤ δ n)
    (hbdy : Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) /
          (boxGraph d n).edgeFinset.card) atTop (nhds 0)) :
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q s)
      atTop (nhds L) := by
  rw [← tendsto_add_atTop_iff_nat
    (f := fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q s) 1]
  have hrepr : (fun n => wpd_avgWiredDensity (boxGraph d (n + 1))
      (boxBoundary d (n + 1)) q s) = fun n =>
      (1 / ((boxGraph d (n + 1)).edgeFinset.card : ℝ)) *
        ∑ e ∈ (boxGraph d (n + 1)).edgeFinset,
          edgeMargProb (wiredFkProb (boxGraph d (n + 1)) (boxBoundary d (n + 1))
            (fsc_logistic s) q) e := by
    funext n
    exact wpd_avgWiredDensity_eq_sum_edgeMarg
      (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q s
  rw [hrepr]
  exact adc_absavg_tendsto
    (ι := fun n => Sym2 (boxVerts d (n + 1)))
    (En := fun n => (boxGraph d (n + 1)).edgeFinset) (fun n => In (n + 1))
    (fn := fun n e => edgeMargProb (wiredFkProb (boxGraph d (n + 1))
      (boxBoundary d (n + 1)) (fsc_logistic s) q) e)
    L (fun n => δ (n + 1)) (fun n => hIE (n + 1))
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_nonneg (boxGraph d (n + 1))
      (boxBoundary d (n + 1)) (fsc_logistic_pos s) (fsc_logistic_lt_one s) hq e)
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d (n + 1))
      (boxBoundary d (n + 1)) (fsc_logistic_pos s) (fsc_logistic_lt_one s) hq e)
    hL0 hL1 (fun n => hδ0 (n + 1)) (hδlim.comp (tendsto_add_atTop_nat 1))
    (fun n => hin (n + 1)) (fun n => hbox1 (n + 1) (by omega))
    (hbdy.comp (tendsto_add_atTop_nat 1))


theorem fkgq_centered_hasDerivAt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (hq : 0 < q)
    (hE : 0 < G.edgeFinset.card) (s : ℝ) :
    HasDerivAt (cfe_centered G q) (fkgq_avgDensity G q s) s := by
  have hbase := ivp2_tiltFreeEnergy_hasDerivAt G q hq hE s
  have hmean := ivp2_cgfMean_eq_openCount_expect G q hq s
  have hderiv : HasDerivAt (ivp2_tiltFreeEnergy G q) (fkgq_avgDensity G q s) s := by
    rw [← hmean] at hbase
    simpa [fkgq_avgDensity] using hbase
  exact hderiv.sub_const (ivp2_tiltFreeEnergy G q 0)


theorem fkgq_wiredCentered_hasDerivAt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (bdry : V → Prop) [DecidablePred bdry]
    (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card) (s : ℝ) :
    HasDerivAt (cfe_wiredCentered G bdry q) (wpd_avgWiredDensity G bdry q s) s := by
  exact (wpd_wiredTiltFreeEnergy_hasDerivAt G bdry q hq hE s).sub_const
    (wpd_wiredTiltFreeEnergy G bdry q 0)


theorem fkgq_wiredCentered_tendsto (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq : 1 ≤ q)
    {G : ℝ → ℝ} (s : ℝ)
    (hfree : Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds (G s))) :
    Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) q s)
      atTop (nhds (G s)) := by
  have hedge : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card :=
    fun n hn => ecz_box_edge_pos d hd hn
  have hsv := fup_surfaceVolume_tendsto_zero d hd
  have hdiff : ∀ u : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d (n + 1)) q u
        - wpd_wiredTiltFreeEnergy (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q u)
      atTop (nhds 0) := by
    intro u
    have hbound : ∀ n, |ivp2_tiltFreeEnergy (boxGraph d (n + 1)) q u
          - wpd_wiredTiltFreeEnergy (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q u|
        ≤ ((Finset.univ.filter (boxBoundary d (n + 1))).card : ℝ)
            / ((boxGraph d (n + 1)).edgeFinset.card : ℝ) * Real.log q := fun n =>
      wpd_tiltFreeEnergy_sub_le (boxGraph d (n + 1)) (boxBoundary d (n + 1)) hq
        (hedge (n + 1) (by omega)) u
    have hsv' := (hsv.mul_const (Real.log q)).comp (tendsto_add_atTop_nat 1)
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr
      (squeeze_zero (fun n => abs_nonneg _) hbound (by simpa using hsv'))
  have hfree' := hfree.comp (tendsto_add_atTop_nat 1)
  have hcdiff : Tendsto (fun n => cfe_centered (boxGraph d (n + 1)) q s
      - cfe_wiredCentered (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q s)
      atTop (nhds 0) := by
    have := (hdiff s).sub (hdiff 0)
    have ht : Tendsto (fun n =>
        (ivp2_tiltFreeEnergy (boxGraph d (n + 1)) q s
          - wpd_wiredTiltFreeEnergy (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q s)
        - (ivp2_tiltFreeEnergy (boxGraph d (n + 1)) q 0
          - wpd_wiredTiltFreeEnergy (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q 0))
        atTop (nhds 0) := by simpa using this
    refine Tendsto.congr' ?_ ht
    filter_upwards with n
    unfold cfe_centered cfe_wiredCentered
    ring
  have hw' : Tendsto (fun n => cfe_wiredCentered (boxGraph d (n + 1))
      (boxBoundary d (n + 1)) q s) atTop (nhds (G s)) := by
    have h := hfree'.sub hcdiff
    have ht : Tendsto (fun n => cfe_centered (boxGraph d (n + 1)) q s
        - (cfe_centered (boxGraph d (n + 1)) q s
          - cfe_wiredCentered (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q s))
        atTop (nhds (G s)) := by simpa using h
    refine Tendsto.congr' ?_ ht
    filter_upwards with n
    ring
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp (by simpa [Nat.add_comm] using hw')


end StatMech.FK
