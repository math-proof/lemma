/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PairedAdjacentBoundaryBandScheduleData.exists_crossNestedOutwardData
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {step : Nat -> Int}
    (scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (hTI : P.IsTranslationInvariant mu)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n)
    (padding : Nat) (lowerX lowerY : Nat -> Nat) :
    exists data : PairedAdjacentCrossNestedOutwardData
        E Edual mu muDual scheduleData pad padding,
      (forall n, lowerX n <= (data.triple n).currentX) /\
      (forall n, lowerY n <= (data.triple n).currentY) := by
  obtain ⟨dualRadius, hdual⟩ :=
    scheduleData.exists_alignedExact_dualOutwardRadius
      hFKGDual hTIDual huniqueDual pad hpad
  have hslack (n : Nat) := exists_pairedAlignedConnectorSlack E Edual
    (scheduleData.family n) (scheduleData.familyDual n)
    (scheduleData.schedule n)
    (max (max (scheduleData.radius n) (dualRadius n)) n)
  let index : Nat -> Nat := fun n => Classical.choose (hslack n)
  let slack : forall n, PairedAlignedConnectorSlack E Edual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n)
      (max (max (scheduleData.radius n) (dualRadius n)) n)
      (index n) := fun n => Classical.choose_spec (hslack n)
  have htriple (n : Nat) :=
    exists_alignedCrossNestedThreePairedMixedBoundaryScores_ge
      E Edual mu muDual hTI hTIDual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n) (index n) padding (lowerX n) (lowerY n)
  let triple : forall n, AlignedCrossNestedThreePairedMixedBoundaryScores
      E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
      (scheduleData.score n) (scheduleData.scoreDual n)
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n) (index n) padding := fun n =>
    Classical.choose (htriple n)
  let data : PairedAdjacentCrossNestedOutwardData
      E Edual mu muDual scheduleData pad padding := {
    dualRadius := dualRadius
    dualOutward := hdual
    index := index
    slack := slack
    triple := triple }
  refine ⟨data, ?_, ?_⟩
  · intro n
    exact (Classical.choose_spec (htriple n)).1
  · intro n
    exact (Classical.choose_spec (htriple n)).2.1


theorem PairedAdjacentCrossNestedOutwardData.local_limits
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {step : Nat -> Int}
    {scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step}
    {pad : Nat -> Int} {padding : Nat}
    (data : PairedAdjacentCrossNestedOutwardData
      E Edual mu muDual scheduleData pad padding)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent 0
        (data.triple n).currentX 0 (data.triple n).currentY))
      (mu.real (E.verticalCrossingEvent
        (data.triple n).current.raw.data.wideLeft
        (data.triple n).current.raw.data.wideRight 0
        ((data.triple n).currentY + (step n).toNat))))
      atTop (nhds 1) /\
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight
        (0 - (pad n : Real))
        (((data.triple n).previousY : Real) + pad n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (0 - (pad n : Real))
        (((data.triple n).previousX : Real) + pad n)
        0 (data.triple n).previousY))) atTop (nhds 1) /\
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (data.triple n).next.raw.data.wideLeft
        (data.triple n).next.raw.data.wideRight
        (0 - (pad n : Real))
        (((data.triple n).nextY : Real) + pad n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (0 - (pad n : Real))
        (((data.triple n).nextX : Real) + pad n)
        0 (data.triple n).nextY))) atTop (nhds 1) := by
  have hprimalSlack : forall n, PairedAlignedConnectorSlack E Edual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n)
      (max (scheduleData.radius n) n) (data.index n) := by
    intro n
    apply (data.slack n).restrictRadius E Edual
    omega
  have hdualSlack : forall n, PairedAlignedConnectorSlack E Edual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n)
      (max (data.dualRadius n) n) (data.index n) := by
    intro n
    apply (data.slack n).restrictRadius E Edual
    omega
  refine ⟨scheduleData.alignedExact_primalAdjacent_limit hFKG hTI
      hunique data.index (fun n => (data.triple n).currentX)
      (fun n => (data.triple n).currentY)
      (fun n => (data.triple n).current) hprimalSlack, ?_, ?_⟩
  · exact data.dualOutward data.index
      (fun n => (data.triple n).previousX)
      (fun n => (data.triple n).previousY)
      (fun n => (data.triple n).previous) hdualSlack
  · exact data.dualOutward data.index
      (fun n => (data.triple n).nextX)
      (fun n => (data.triple n).nextY)
      (fun n => (data.triple n).next) hdualSlack


theorem PairedAdjacentCrossNestedOutwardData.shifted_matched_inequalities
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {step : Nat -> Int}
    {scheduleData : PairedAdjacentBoundaryBandScheduleData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) step}
    {pad : Nat -> Int} {padding : Nat}
    (data : PairedAdjacentCrossNestedOutwardData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      scheduleData pad padding)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (hpadding : 4 * B <= (padding : Real))
    (hcurrentX : forall n, 10 * B < (data.triple n).currentX)
    (hcurrentY : forall n, 10 * B < (data.triple n).currentY) :
    (forall n,
      mu.real (D.primalEmbedding.horizontalCrossingEvent 0
          (data.triple n).currentX 0 (data.triple n).currentY) +
        (D.dualMeasure mu).real
          (D.dualEmbedding.verticalCrossingEvent
            (data.triple n).previous.raw.data.wideLeft
            (data.triple n).previous.raw.data.wideRight 0
            (data.triple n).previousY) <= 1) /\
    (forall n,
      mu.real (D.primalEmbedding.verticalCrossingEvent
          (data.triple n).current.raw.data.wideLeft
          (data.triple n).current.raw.data.wideRight 0
          (data.triple n).currentY) +
        (D.dualMeasure mu).real
          (D.dualEmbedding.horizontalCrossingEvent 0
            (data.triple n).nextX 0 (data.triple n).nextY) <= 1) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  constructor
  · intro n
    let z : Site 2 := fun i => if i = 0 then
      padding - (data.triple n).previous.raw.wideLeftInt
      else -(padding : Int)
    have hcurrentXR : ((data.triple n).currentX : Real) =
        ((data.triple n).previous.raw.wideRightInt : Real) -
          (data.triple n).previous.raw.wideLeftInt + 2 * padding := by
      exact_mod_cast (data.triple n).currentX_eq
    have hpreviousYR : ((data.triple n).previousY : Real) =
        (data.triple n).currentY + 2 * padding := by
      exact_mod_cast (data.triple n).previousY_eq
    have hspanX : (0 : Real) + 5 * B <
        (data.triple n).currentX - 5 * B := by
      linarith [hcurrentX n]
    have hpad0 : (0 : Real) <= padding := by positivity
    have hspanY : -(padding : Real) + 5 * B <
        (data.triple n).currentY + padding - 5 * B := by
      linarith [hcurrentY n]
    have hbase := D.matchedCrossing_measureReal_add_le_one_of_pads
      mu hBpos hBp hBd hpadding hpadding hspanX hspanY
    have htranslated :=
      D.dualEmbedding.verticalCrossing_translate_measureReal_le
        (D.dualMeasure mu) hTIDual z
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
    have hdualLe :
        (D.dualMeasure mu).real
            (D.dualEmbedding.verticalCrossingEvent
              (data.triple n).previous.raw.data.wideLeft
              (data.triple n).previous.raw.data.wideRight 0
              (data.triple n).previousY) <=
          (D.dualMeasure mu).real
            (D.dualEmbedding.verticalCrossingEvent
              padding ((data.triple n).currentX - padding)
              (-padding) ((data.triple n).currentY + padding)) := by
      calc
        _ <= (D.dualMeasure mu).real
            (D.dualEmbedding.verticalCrossingEvent
              ((data.triple n).previous.raw.data.wideLeft + (z 0 : Real))
              ((data.triple n).previous.raw.data.wideRight + (z 0 : Real))
              (0 + (z 1 : Real))
              ((data.triple n).previousY + (z 1 : Real))) := htranslated
        _ = _ := by
          apply congrArg (fun event : Set (ConfigSpace (Sym2 W)) =>
            (D.dualMeasure mu).real event)
          congr 1
          all_goals
            simp only [z, Pi.zero_apply, if_pos, if_neg]
          · rw [(data.triple n).previous.raw.wideLeft_eq]
            push_cast
            ring
          · rw [(data.triple n).previous.raw.wideRight_eq]
            push_cast
            linarith [hcurrentXR]
          · push_cast
            ring
          · push_cast
            linarith [hpreviousYR]
    simp_rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)] at hdualLe
    have hbase' :
        mu.real (D.primalEmbedding.horizontalCrossingEvent 0
            (data.triple n).currentX 0 (data.triple n).currentY) +
          mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
            D.dualEmbedding.verticalCrossingEvent
              padding ((data.triple n).currentX - padding)
              (-padding) ((data.triple n).currentY + padding)) <= 1 := by
      simpa only [zero_add, neg_add_cancel, sub_neg_eq_add,
        add_sub_cancel_right, sub_add_cancel] using hbase
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
    linarith
  · intro n
    let z : Site 2 := fun i => if i = 0 then
      (data.triple n).current.raw.wideLeftInt - padding
      else (padding : Int)
    have hnextXR : ((data.triple n).nextX : Real) =
        ((data.triple n).current.raw.wideRightInt : Real) -
          (data.triple n).current.raw.wideLeftInt + 2 * padding := by
      exact_mod_cast (data.triple n).nextX_eq
    have hcurrentYR : ((data.triple n).currentY : Real) =
        (data.triple n).nextY + 2 * padding := by
      exact_mod_cast (data.triple n).currentY_eq
    have hwideSpan : ((data.triple n).currentX : Real) <=
        (data.triple n).current.raw.wideRightInt -
          (data.triple n).current.raw.wideLeftInt := by
      exact_mod_cast (data.triple n).current.raw.extentX_le_wideSpan
    have hspanX :
        (data.triple n).current.raw.data.wideLeft - padding + 5 * B <
          (data.triple n).current.raw.data.wideRight + padding - 5 * B := by
      rw [(data.triple n).current.raw.wideLeft_eq,
        (data.triple n).current.raw.wideRight_eq]
      push_cast
      have hpad0 : (0 : Real) <= padding := by positivity
      linarith [hcurrentX n]
    have hspanY : (0 : Real) + 5 * B <
        (data.triple n).currentY - 5 * B := by
      linarith [hcurrentY n]
    have hbase :=
      D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads
        mu hBpos hBp hBd hpadding hpadding hspanX hspanY
    have htranslated :=
      D.dualEmbedding.horizontalCrossing_translate_measureReal_le
        (D.dualMeasure mu) hTIDual z 0 (data.triple n).nextX 0
        (data.triple n).nextY
    have hdualLe :
        (D.dualMeasure mu).real
            (D.dualEmbedding.horizontalCrossingEvent 0
              (data.triple n).nextX 0 (data.triple n).nextY) <=
          (D.dualMeasure mu).real
            (D.dualEmbedding.horizontalCrossingEvent
              ((data.triple n).current.raw.data.wideLeft - padding)
              ((data.triple n).current.raw.data.wideRight + padding)
              padding ((data.triple n).currentY - padding)) := by
      calc
        _ <= (D.dualMeasure mu).real
            (D.dualEmbedding.horizontalCrossingEvent
              (0 + (z 0 : Real))
              ((data.triple n).nextX + (z 0 : Real))
              (0 + (z 1 : Real))
              ((data.triple n).nextY + (z 1 : Real))) := htranslated
        _ = _ := by
          apply congrArg (fun event : Set (ConfigSpace (Sym2 W)) =>
            (D.dualMeasure mu).real event)
          congr 1
          all_goals
            simp only [z, Pi.zero_apply, if_pos, if_neg]
          · rw [(data.triple n).current.raw.wideLeft_eq]
            push_cast
            ring
          · rw [(data.triple n).current.raw.wideRight_eq]
            push_cast
            linarith [hnextXR]
          · push_cast
            ring
          · push_cast
            linarith [hcurrentYR]
    simp_rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)] at hdualLe
    have hbase' :
        mu.real (D.primalEmbedding.verticalCrossingEvent
            (data.triple n).current.raw.data.wideLeft
            (data.triple n).current.raw.data.wideRight 0
            (data.triple n).currentY) +
          mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
            D.dualEmbedding.horizontalCrossingEvent
              ((data.triple n).current.raw.data.wideLeft - padding)
              ((data.triple n).current.raw.data.wideRight + padding)
              padding ((data.triple n).currentY - padding)) <= 1 := by
      simpa only [zero_add, add_sub_cancel_right, sub_add_cancel] using hbase
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
    linarith


theorem adjacent_height_array_contradiction_of_primal_dual_bounded_limits_of_bounded_matches
    (horizontal vertical dualVertical dualHorizontal : Nat -> Nat -> Real)
    (K : Nat -> Nat)
    (hhorizontal_nonneg : forall n k, 0 <= horizontal n k)
    (hvertical_nonneg : forall n k, 0 <= vertical n k)
    (hhorizontal_le_one : forall n k, horizontal n k <= 1)
    (hvertical_le_one : forall n k, vertical n k <= 1)
    (hvertical_start : Tendsto (fun n => vertical n 0) atTop (nhds 1))
    (hhorizontal_end : Tendsto (fun n => horizontal n (K n + 1))
      atTop (nhds 1))
    (hmatchHorizontal : forall n k, k <= K n + 1 ->
      horizontal n k + dualVertical n k <= 1)
    (hmatchVertical : forall n k, k <= K n + 1 ->
      vertical n k + dualHorizontal n k <= 1)
    (hprimalLimits : forall k : Nat -> Nat,
      (forall n, k n < K n + 1) -> Tendsto (fun n => max
        (horizontal n (k n)) (vertical n (k n + 1)))
        atTop (nhds 1))
    (hdualLimits : forall k : Nat -> Nat,
      (forall n, k n <= K n + 1) -> Tendsto (fun n => max
        (dualVertical n (k n)) (dualHorizontal n (k n)))
        atTop (nhds 1)) : False := by
  apply adjacent_height_array_contradiction_of_endpoint_and_uniform_limits
    horizontal vertical K hhorizontal_nonneg hvertical_nonneg
    hhorizontal_le_one hvertical_le_one hvertical_start hhorizontal_end
  intro k hk
  have hkBound : forall n, k n <= K n + 1 := fun n => (hk n).le
  have hkNextBound : forall n, k n + 1 <= K n + 1 := by
    intro n
    exact Nat.succ_le_of_lt (hk n)
  refine ⟨hprimalLimits k hk, ?_, ?_⟩
  · simpa only [min_comm] using min_tendsto_zero_of_matched_exclusion
      (fun n => horizontal n (k n))
      (fun n => vertical n (k n))
      (fun n => dualVertical n (k n))
      (fun n => dualHorizontal n (k n))
      (fun n => hhorizontal_nonneg n (k n))
      (fun n => hvertical_nonneg n (k n))
      (fun n => hmatchHorizontal n (k n) (hkBound n))
      (fun n => hmatchVertical n (k n) (hkBound n))
      (hdualLimits k hkBound)
  · simpa only [min_comm] using min_tendsto_zero_of_matched_exclusion
      (fun n => horizontal n (k n + 1))
      (fun n => vertical n (k n + 1))
      (fun n => dualVertical n (k n + 1))
      (fun n => dualHorizontal n (k n + 1))
      (fun n => hhorizontal_nonneg n (k n + 1))
      (fun n => hvertical_nonneg n (k n + 1))
      (fun n => hmatchHorizontal n (k n + 1) (hkNextBound n))
      (fun n => hmatchVertical n (k n + 1) (hkNextBound n))
      (hdualLimits (fun n => k n + 1) hkNextBound)


theorem shifted_crossNested_array_contradiction_of_bounded_limits
    (horizontal vertical dualVertical dualHorizontal : Nat -> Nat -> Real)
    (K : Nat -> Nat)
    (hhorizontal_nonneg : forall n k, 0 <= horizontal n k)
    (hvertical_nonneg : forall n k, 0 <= vertical n k)
    (hhorizontal_le_one : forall n k, horizontal n k <= 1)
    (hvertical_le_one : forall n k, vertical n k <= 1)
    (hvertical_start : Tendsto (fun n => vertical n 0)
      atTop (nhds 1))
    (hhorizontal_end : Tendsto (fun n =>
      horizontal n (2 * (K n + 1) + 2)) atTop (nhds 1))
    (hmatchHorizontal : forall n k, k < 2 * (K n + 1) + 2 ->
      horizontal n (k + 1) + dualVertical n k <= 1)
    (hmatchVertical : forall n k, k < 2 * (K n + 1) + 2 ->
      vertical n k + dualHorizontal n (k + 1) <= 1)
    (hprimalLimits : forall k : Nat -> Nat,
      (forall n, k n < K n + 1) -> Tendsto (fun n => max
        (horizontal n (2 * k n + 2))
        (vertical n (2 * k n + 2))) atTop (nhds 1))
    (hdualLimits : forall k : Nat -> Nat,
      (forall n, k n <= K n + 1) -> Tendsto (fun n => max
        (dualVertical n (2 * k n + 1))
        (dualHorizontal n (2 * k n + 1))) atTop (nhds 1)) : False := by
  let horizontal' : Nat -> Nat -> Real := fun n k =>
    horizontal n (2 * k + 2)
  let vertical' : Nat -> Nat -> Real := fun n k =>
    vertical n (2 * k)
  let dualVertical' : Nat -> Nat -> Real := fun n k =>
    dualVertical n (2 * k + 1)
  let dualHorizontal' : Nat -> Nat -> Real := fun n k =>
    dualHorizontal n (2 * k + 1)
  apply adjacent_height_array_contradiction_of_primal_dual_bounded_limits_of_bounded_matches
    horizontal' vertical' dualVertical' dualHorizontal' K
  · intro n k
    exact hhorizontal_nonneg n _
  · intro n k
    exact hvertical_nonneg n _
  · intro n k
    exact hhorizontal_le_one n _
  · intro n k
    exact hvertical_le_one n _
  · simpa only [vertical', mul_zero] using hvertical_start
  · simpa only [horizontal'] using hhorizontal_end
  · intro n k hk
    simpa only [horizontal', dualVertical'] using
      hmatchHorizontal n (2 * k + 1) (by omega)
  · intro n k hk
    simpa only [vertical', dualHorizontal'] using
      hmatchVertical n (2 * k) (by omega)
  · intro k hk
    simpa only [horizontal', vertical', Nat.mul_add,
      Nat.mul_one, Nat.add_assoc] using hprimalLimits k hk
  · intro k hk
    simpa only [dualVertical', dualHorizontal'] using hdualLimits k hk


end StatMech.FK.PeriodicPlanar
