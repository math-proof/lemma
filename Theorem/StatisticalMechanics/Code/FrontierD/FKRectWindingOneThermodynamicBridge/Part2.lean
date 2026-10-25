/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingOneResidualLower
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorThermodynamicBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectUnitLeftBarrier.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceChainWindingUpper.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectWindingOneThermodynamicBridge.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem FKRectWindingOneSource.connectionProduct_pos
    {R : FKRectTorus} {q : Real} (source : FKRectWindingOneSource R q)
    (hq : 0 < q) :
    0 < source.connectionProduct := by
  exact fkRectRightBandConnectionProduct_pos R source.cut hq source.pairs
    source.pair_reachable


theorem FKRectWindingOneSource.connectionProduct_negLogRate_le
    {R : FKRectTorus} {q a : Real} (source : FKRectWindingOneSource R q)
    (ha : 0 < a)
    (hlower : ∀ xy ∈ source.pairs, a <=
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectRightStripBand R source.cut 1 (R.height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2) :
    -Real.log source.connectionProduct / R.height <=
      (source.pairs.card : Real) * (-Real.log a) / R.height := by
  have hprod : a ^ source.pairs.card <= source.connectionProduct := by
    rw [show a ^ source.pairs.card = ∏ _xy ∈ source.pairs, a by simp]
    unfold FKRectWindingOneSource.connectionProduct
    exact Finset.prod_le_prod (fun _ _ => ha.le) hlower
  have hlog := Real.log_le_log (pow_pos ha _) hprod
  rw [Real.log_pow] at hlog
  have hnum : -Real.log source.connectionProduct <=
      (source.pairs.card : Real) * (-Real.log a) := by
    linarith
  exact div_le_div_of_nonneg_right hnum (by positivity)


theorem FKRectWindingOneSource.connectionProduct_negLogRate_le_of_mul_pow
    {R : FKRectTorus} {q C a : Real} (source : FKRectWindingOneSource R q)
    (n : Nat) (hC : 0 < C) (ha : 0 < a)
    (hlower : C * a ^ n <= source.connectionProduct) :
    -Real.log source.connectionProduct / R.height <=
      ((n : Real) * (-Real.log a) + (-Real.log C)) / R.height := by
  have hCa : 0 < C * a ^ n := mul_pos hC (pow_pos ha n)
  have hlog := Real.log_le_log hCa hlower
  rw [Real.log_mul hC.ne' (pow_pos ha n).ne', Real.log_pow] at hlog
  have hnum : -Real.log source.connectionProduct <=
      (n : Real) * (-Real.log a) + (-Real.log C) := by
    linarith
  exact div_le_div_of_nonneg_right hnum (by positivity)


theorem FKRectWindingOneSource.connectionProduct_negLogRate_le_of_card
    {R : FKRectTorus} {q a : Real} (source : FKRectWindingOneSource R q)
    (blocks : Nat) (hcard : source.pairs.card <= blocks)
    (ha : 0 < a) (ha1 : a <= 1)
    (hlower : ∀ xy ∈ source.pairs, a <=
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectRightStripBand R source.cut 1 (R.height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2) :
    -Real.log source.connectionProduct / R.height <=
      (blocks : Real) * (-Real.log a) / R.height := by
  have hbase := source.connectionProduct_negLogRate_le ha hlower
  have hcost : 0 <= -Real.log a := by
    linarith [Real.log_nonpos ha.le ha1]
  have hcardReal : (source.pairs.card : Real) <= blocks := by
    exact_mod_cast hcard
  have hmul : (source.pairs.card : Real) * (-Real.log a) <=
      (blocks : Real) * (-Real.log a) :=
    mul_le_mul_of_nonneg_right hcardReal hcost
  exact hbase.trans (div_le_div_of_nonneg_right hmul (by positivity))

theorem FKRectWindingOneSource.barrierMass_pos
    {R : FKRectTorus} {q : Real} (source : FKRectWindingOneSource R q)
    (hq : 0 < q) :
    0 < source.barrierMass := by
  exact fkRectCriticalEventMass_pos_of_mem R hq _
    source.barrierConfiguration source.barrier_mem

theorem FKRectWindingOneSource.windingOneMass_pos
    {R : FKRectTorus} {q : Real} (source : FKRectWindingOneSource R q)
    (hq : 1 <= q) :
    0 < fkRectCriticalWindingOneMass R q := by
  exact fkRectCriticalWindingOneMass_pos_of_source R
    source.leftRight source.cut source.sep source.left hq source.gap_mem
    source.x source.x_right source.chosen source.pairs
    source.chain_spans
    (source.connectionProduct_pos (zero_lt_one.trans_le hq))
    (source.barrierMass_pos (zero_lt_one.trans_le hq))


theorem fkRectCriticalWindingOneMass_pos
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) :
    0 < fkRectCriticalWindingOneMass R q :=
  (fkRectUnitWindingOneSource R q).windingOneMass_pos hq

theorem fkRectSourceLeftBarrier_mass_pos_of_one_le
    (R : FKRectTorus) (right : Nat) (hone : 1 <= right)
    (hright : right + 1 < R.width) {q : Real} (hq : 0 < q) :
    0 < fkRectCriticalEventMass R q
      (fkRectSourceLeftBarrier R right (fkRectUnitLeftBarrierGap R)) :=
  fkRectCriticalEventMass_pos_of_mem R hq _
    (fkRectUnitLeftBarrierConfiguration R)
    (fkRectUnitLeftBarrierConfiguration_mem_source_of_one_le
      R right hone hright)

theorem FKRectWindingOneSource.windingOne_negLogRate_le
    {R : FKRectTorus} {q : Real} (source : FKRectWindingOneSource R q)
    (hq : 1 <= q) :
    -Real.log (fkRectCriticalWindingOneMass R q) / R.height <=
      -Real.log source.connectionProduct / R.height +
        -Real.log source.barrierMass / R.height +
        -Real.log (FK.cFE (fkRectCriticalP q) q) / R.height := by
  exact windingOne_negLogRate_le_source_cost R
    source.leftRight source.cut source.sep source.left hq source.gap_mem
    source.x source.x_right source.chosen source.pairs
    source.chain_spans
    (source.connectionProduct_pos (zero_lt_one.trans_le hq))
    (source.barrierMass_pos (zero_lt_one.trans_le hq))


theorem chargeOne_negLogRate_le_windingOne_add_constant
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (hmass : 0 < fkRectCriticalWindingOneMass R q) :
    -Real.log
          (sixVertexTorusFixedChargePartitionSum R.medialTorus 1
                (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum R.medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        R.height <=
      -Real.log (fkRectCriticalWindingOneMass R q) / R.height +
        (Real.log
              (fkRectChargeOneModeCost
                (sixVertexAntiferroelectricLambda
                  (fkQgt4SixVertexWeight q)) ^ 2) -
            Real.log ((2 / Real.sqrt q) ^ 2 / q)) /
          R.height := by
  let c : Real := (2 / Real.sqrt q) ^ 2 / q
  let K : Real := fkRectChargeOneModeCost
    (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))
  let Q : Real :=
    sixVertexTorusFixedChargePartitionSum R.medialTorus 1
          (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) /
      sixVertexTorusFixedChargePartitionSum R.medialTorus 0
          (Nat.zero_le _) (fkQgt4SixVertexWeight q)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hK : 0 < K ^ 2 := by
    exact sq_pos_of_pos (lt_of_lt_of_le zero_lt_one
      (fkRectChargeOneModeCost_one_le _))
  have hQ : 0 < Q := by
    dsimp [Q]
    apply div_pos
    · rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
      exact sixVertexSector_trace_pow_pos
        ((Nat.sub_le _ _).trans
          (Nat.div_le_self R.medialTorus.width 2))
        (by linarith [two_lt_fkQgt4SixVertexWeight hq])
        R.medialTorus.height
    · rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace]
      exact sixVertexSector_trace_pow_pos
        (Nat.div_le_self R.medialTorus.width 2)
        (by linarith [two_lt_fkQgt4SixVertexWeight hq])
        R.medialTorus.height
  have hfinite : c * fkRectCriticalWindingOneMass R q <= K ^ 2 * Q := by
    simpa [c, K, Q, fkRectCriticalWindingOneMass] using
      (windingOneResidual_mul_mass_le_modeCost_sq_mul_chargeOneRatio R hq)
  have hlog := Real.log_le_log (mul_pos hc hmass) hfinite
  rw [Real.log_mul hc.ne' hmass.ne', Real.log_mul hK.ne' hQ.ne'] at hlog
  have hnum :
      -Real.log Q <= -Real.log (fkRectCriticalWindingOneMass R q) +
        (Real.log (K ^ 2) - Real.log c) := by
    linarith
  have hh : 0 <= (R.height : Real) := by positivity
  calc
    -Real.log Q / R.height <=
        (-Real.log (fkRectCriticalWindingOneMass R q) +
          (Real.log (K ^ 2) - Real.log c)) / R.height :=
      div_le_div_of_nonneg_right hnum hh
    _ = -Real.log (fkRectCriticalWindingOneMass R q) / R.height +
        (Real.log (K ^ 2) - Real.log c) / R.height := by ring
    _ = _ := by rfl


theorem chargeOneRate_le_windingOneRate_of_tendsto
    (R : Nat -> FKRectTorus) {q chargeRate windingRate : Real}
    (hq : 4 < q)
    (hmass : forall n, 0 < fkRectCriticalWindingOneMass (R n) q)
    (hheight : Tendsto (fun n => ((R n).height : Real)) atTop atTop)
    (hcharge : Tendsto (fun n =>
      -Real.log
          (sixVertexTorusFixedChargePartitionSum (R n).medialTorus 1
                (one_le_fkRectMedial_halfWidth (R n)) (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum (R n).medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (R n).height) atTop (nhds chargeRate))
    (hwind : Tendsto (fun n =>
      -Real.log (fkRectCriticalWindingOneMass (R n) q) /
        (R n).height) atTop (nhds windingRate)) :
    chargeRate <= windingRate := by
  let C : Real :=
    Real.log
        (fkRectChargeOneModeCost
          (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) ^ 2) -
      Real.log ((2 / Real.sqrt q) ^ 2 / q)
  have hconstant : Tendsto (fun n => C / ((R n).height : Real))
      atTop (nhds 0) := hheight.const_div_atTop C
  have hright := hwind.add hconstant
  have hle : chargeRate <= windingRate + 0 := by
    apply le_of_tendsto_of_tendsto hcharge hright
    filter_upwards [] with n
    simpa [C] using
      chargeOne_negLogRate_le_windingOne_add_constant (R n) hq (hmass n)
  simpa using hle


theorem le_of_tendsto_of_eventually_le_add_vanishing
    (f g error : Nat -> Real) {limit upper : Real}
    (hf : Tendsto f atTop (nhds limit))
    (herror : Tendsto error atTop (nhds 0))
    (hle : ∀ᶠ n in atTop, f n <= g n + error n)
    (hg : forall epsilon : Real, 0 < epsilon ->
      ∀ᶠ n in atTop, g n <= upper + epsilon) :
    limit <= upper := by
  by_contra hnot
  have hgap : 0 < limit - upper := sub_pos.mpr (lt_of_not_ge hnot)
  let epsilon : Real := (limit - upper) / 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hflow : ∀ᶠ n in atTop, limit - epsilon < f n :=
    (tendsto_order.1 hf).1 (limit - epsilon) (by linarith)
  have herr : ∀ᶠ n in atTop, error n < epsilon :=
    (tendsto_order.1 herror).2 epsilon hepsilon
  obtain ⟨n, hn, hgn, hfn, hen⟩ :=
    (hle.and ((hg epsilon hepsilon).and (hflow.and herr))).exists
  dsimp [epsilon] at hgn hfn hen
  linarith


theorem chargeOneRate_le_of_windingOne_eventualUpper
    (R : Nat -> FKRectTorus) {q chargeRate windingUpper : Real}
    (hq : 4 < q)
    (hmass : forall n, 0 < fkRectCriticalWindingOneMass (R n) q)
    (hheight : Tendsto (fun n => ((R n).height : Real)) atTop atTop)
    (hcharge : Tendsto (fun n =>
      -Real.log
          (sixVertexTorusFixedChargePartitionSum (R n).medialTorus 1
                (one_le_fkRectMedial_halfWidth (R n)) (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum (R n).medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (R n).height) atTop (nhds chargeRate))
    (hwind : forall epsilon : Real, 0 < epsilon -> ∀ᶠ n in atTop,
      -Real.log (fkRectCriticalWindingOneMass (R n) q) /
          (R n).height <= windingUpper + epsilon) :
    chargeRate <= windingUpper := by
  let charge : Nat -> Real := fun n =>
    -Real.log
          (sixVertexTorusFixedChargePartitionSum (R n).medialTorus 1
                (one_le_fkRectMedial_halfWidth (R n)) (fkQgt4SixVertexWeight q) /
            sixVertexTorusFixedChargePartitionSum (R n).medialTorus 0
                (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
        (R n).height
  let winding : Nat -> Real := fun n =>
    -Real.log (fkRectCriticalWindingOneMass (R n) q) / (R n).height
  let C : Real :=
    Real.log
        (fkRectChargeOneModeCost
          (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) ^ 2) -
      Real.log ((2 / Real.sqrt q) ^ 2 / q)
  let error : Nat -> Real := fun n => C / ((R n).height : Real)
  have herror : Tendsto error atTop (nhds 0) := by
    exact hheight.const_div_atTop C
  apply le_of_tendsto_of_eventually_le_add_vanishing
    charge winding error hcharge herror
  · filter_upwards [] with n
    simpa [charge, winding, error, C] using
      chargeOne_negLogRate_le_windingOne_add_constant (R n) hq (hmass n)
  · intro epsilon hepsilon
    simpa [winding] using hwind epsilon hepsilon


theorem fixedChargeVertical_chargeOneRate_le_windingOneRate
    {q windingRate : Real} (hq : 4 < q) (k : Nat)
    (hmass : forall m, 0 < fkRectCriticalWindingOneMass
      (fkRectFixedChargeVerticalFamily 1 k m) q)
    (hwind : Tendsto (fun m =>
      -Real.log (fkRectCriticalWindingOneMass
          (fkRectFixedChargeVerticalFamily 1 k m) q) /
        (fkRectFixedChargeVerticalFamily 1 k m).height)
      atTop (nhds windingRate)) :
    -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) 1 (k + 1) <= windingRate := by
  let R : Nat -> FKRectTorus := fkRectFixedChargeVerticalFamily 1 k
  have hheightNat : Tendsto (fun m => (R m).height) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 <| ⟨N, fun m hm => by
      dsimp [R]
      omega⟩
  have hheight : Tendsto (fun m => ((R m).height : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hheightNat
  apply chargeOneRate_le_windingOneRate_of_tendsto R hq hmass hheight
  · simpa [R] using fkRectFixedCharge_vertical_negLogRatio_tendsto
      (show 0 < fkQgt4SixVertexWeight q by
        linarith [two_lt_fkQgt4SixVertexWeight hq]) 1 k
  · simpa [R] using hwind


theorem fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper
    {q windingUpper : Real} (hq : 4 < q) (k : Nat)
    (hmass : forall m, 0 < fkRectCriticalWindingOneMass
      (fkRectFixedChargeVerticalFamily 1 k m) q)
    (hwind : forall epsilon : Real, 0 < epsilon -> ∀ᶠ m in atTop,
      -Real.log (fkRectCriticalWindingOneMass
          (fkRectFixedChargeVerticalFamily 1 k m) q) /
          (fkRectFixedChargeVerticalFamily 1 k m).height <=
        windingUpper + epsilon) :
    -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) 1 (k + 1) <= windingUpper := by
  let R : Nat -> FKRectTorus := fkRectFixedChargeVerticalFamily 1 k
  have hheightNat : Tendsto (fun m => (R m).height) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 <| ⟨N, fun m hm => by
      dsimp [R]
      omega⟩
  have hheight : Tendsto (fun m => ((R m).height : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hheightNat
  apply chargeOneRate_le_of_windingOne_eventualUpper R hq hmass hheight
  · simpa [R] using fkRectFixedCharge_vertical_negLogRatio_tendsto
      (show 0 < fkQgt4SixVertexWeight q by
        linarith [two_lt_fkQgt4SixVertexWeight hq]) 1 k
  · intro epsilon hepsilon
    simpa [R] using hwind epsilon hepsilon


theorem fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper_unconditional
    {q windingUpper : Real} (hq : 4 < q) (k : Nat)
    (hwind : forall epsilon : Real, 0 < epsilon -> ∀ᶠ m in atTop,
      -Real.log (fkRectCriticalWindingOneMass
          (fkRectFixedChargeVerticalFamily 1 k m) q) /
          (fkRectFixedChargeVerticalFamily 1 k m).height <=
        windingUpper + epsilon) :
    -sixVertexFixedChargeLogRatio
        (fkQgt4SixVertexWeight q) 1 (k + 1) <= windingUpper :=
  fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper hq k
    (fun m => fkRectCriticalWindingOneMass_pos _ (by linarith)) hwind


theorem fkQgt4SixVertexGapRate_le_of_chargeOneVerticalBounds
    {q xiInv : Real} (hq : 4 < q)
    (hbound : forall k : Nat,
      -sixVertexFixedChargeLogRatio
          (fkQgt4SixVertexWeight q) 1 (k + 1) <= xiInv) :
    fkQgt4SixVertexGapRate q <= xiInv := by
  have hle : ((1 : Nat) : Real) * fkQgt4SixVertexGapRate q <= xiInv :=
    le_of_tendsto
      (tendsto_fkQgt4SixVertexFixedCharge_negLogRatio_gap hq 1 (by omega))
      (Filter.Eventually.of_forall hbound)
  simpa using hle


theorem fkQgt4SixVertexGapRate_le_of_verticalWindingOneEventualUpper
    {q xiInv : Real} (hq : 4 < q)
    (hmass : forall k m, 0 < fkRectCriticalWindingOneMass
      (fkRectFixedChargeVerticalFamily 1 k m) q)
    (hwind : forall k (epsilon : Real), 0 < epsilon -> ∀ᶠ m in atTop,
      -Real.log (fkRectCriticalWindingOneMass
          (fkRectFixedChargeVerticalFamily 1 k m) q) /
          (fkRectFixedChargeVerticalFamily 1 k m).height <=
        xiInv + epsilon) :
    fkQgt4SixVertexGapRate q <= xiInv := by
  apply fkQgt4SixVertexGapRate_le_of_chargeOneVerticalBounds hq
  intro k
  exact fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper
    hq k (hmass k) (hwind k)


theorem fkQgt4SixVertexGapRate_le_of_verticalWindingOneEventualUpper_unconditional
    {q xiInv : Real} (hq : 4 < q)
    (hwind : forall k (epsilon : Real), 0 < epsilon -> ∀ᶠ m in atTop,
      -Real.log (fkRectCriticalWindingOneMass
          (fkRectFixedChargeVerticalFamily 1 k m) q) /
          (fkRectFixedChargeVerticalFamily 1 k m).height <=
        xiInv + epsilon) :
    fkQgt4SixVertexGapRate q <= xiInv := by
  apply fkQgt4SixVertexGapRate_le_of_chargeOneVerticalBounds hq
  intro k
  exact fixedChargeVertical_chargeOneRate_le_windingOneEventualUpper_unconditional
    hq k (hwind k)


theorem fkQgt4SixVertexGapRate_le_of_sourceCostEventualUpper
    {q xiInv : Real} (hq : 4 < q)
    (source : forall k m,
      FKRectWindingOneSource (fkRectFixedChargeVerticalFamily 1 k m) q)
    (hsourceCost : forall k (epsilon : Real), 0 < epsilon -> ∀ᶠ m in atTop,
      -Real.log (source k m).connectionProduct /
            (fkRectFixedChargeVerticalFamily 1 k m).height +
          -Real.log (source k m).barrierMass /
            (fkRectFixedChargeVerticalFamily 1 k m).height <=
        xiInv + epsilon) :
    fkQgt4SixVertexGapRate q <= xiInv := by
  apply fkQgt4SixVertexGapRate_le_of_verticalWindingOneEventualUpper hq
  · intro k m
    exact (source k m).windingOneMass_pos (by linarith)
  · intro k epsilon hepsilon
    let R : Nat -> FKRectTorus := fkRectFixedChargeVerticalFamily 1 k
    let c : Real := FK.cFE (fkRectCriticalP q) q
    let error : Nat -> Real := fun m => -Real.log c / ((R m).height : Real)
    have hheightNat : Tendsto (fun m => (R m).height) atTop atTop := by
      refine tendsto_atTop.2 (fun N => ?_)
      exact eventually_atTop.2 <| ⟨N, fun m hm => by
        dsimp [R]
        omega⟩
    have hheight : Tendsto (fun m => ((R m).height : Real)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hheightNat
    have herror : Tendsto error atTop (nhds 0) := by
      exact hheight.const_div_atTop (-Real.log c)
    let delta : Real := epsilon / 2
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have herr : ∀ᶠ m in atTop, error m < delta :=
      (tendsto_order.1 herror).2 delta hdelta
    filter_upwards [hsourceCost k delta hdelta, herr] with m hcost hmerror
    have hfinite := (source k m).windingOne_negLogRate_le
      (by linarith : 1 <= q)
    simp only [fkRectFixedChargeVerticalFamily_height] at hfinite
    dsimp [R, error, c] at hmerror
    dsimp [delta] at hcost hmerror
    change -Real.log (fkRectCriticalWindingOneMass
        (fkRectFixedChargeVerticalFamily 1 k m) q) /
      ((2 * (m + 2) : Nat) : Real) <= xiInv + epsilon
    linarith

end
end StatMech.FrontierD
