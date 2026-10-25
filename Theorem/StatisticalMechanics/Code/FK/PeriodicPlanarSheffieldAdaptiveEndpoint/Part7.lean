/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part5
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PairedAdjacentBoundaryBandScheduleData.exists_crossNestedOutwardArrayData
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
    (padding : Nat) (K lowerX lowerY : Nat -> Nat) :
    exists data : PairedAdjacentCrossNestedOutwardArrayData
        E Edual mu muDual scheduleData padding K,
      (forall n j, lowerX n <= (data.chain n).extentX j) /\
      (forall n j, lowerY n <= (data.chain n).extentY j) := by
  obtain ⟨dualRadius, hdual⟩ :=
    scheduleData.exists_alignedExact_dualOutwardRadius
      hFKGDual hTIDual huniqueDual (fun _ => 0) (fun _ => le_rfl)
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
  have hchain (n : Nat) := exists_alignedCrossNestedPairedChain_ge
    E Edual mu muDual hTI hTIDual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n) (index n) padding (2 * (K n + 1) + 2)
      (lowerX n) (lowerY n)
  let chain : forall n, AlignedCrossNestedPairedChain E Edual mu muDual
      (P.orbitBox n) (Pdual.orbitBox n)
      (scheduleData.score n) (scheduleData.scoreDual n)
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n) (index n) padding
        (2 * (K n + 1) + 2) := fun n => Classical.choose (hchain n)
  have hdual' :
      forall (k extentX extentY : Nat -> Nat)
        (exact : forall n, AlignedExactExtentPairedMixedBoundaryScores
          E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
          (scheduleData.score n) (scheduleData.scoreDual n)
          (scheduleData.family n) (scheduleData.familyDual n)
          (scheduleData.schedule n) (k n) (extentX n) (extentY n)),
        (forall n, PairedAlignedConnectorSlack E Edual
          (scheduleData.family n) (scheduleData.familyDual n)
          (scheduleData.schedule n) (max (dualRadius n) n) (k n)) ->
        Tendsto (fun n => max
          (muDual.real (Edual.verticalCrossingEvent
            (exact n).raw.data.wideLeft (exact n).raw.data.wideRight
            0 (extentY n)))
          (muDual.real (Edual.horizontalCrossingEvent
            0 (extentX n) 0 (extentY n)))) atTop (nhds 1) := by
    intro k extentX extentY exact hslackDual
    simpa only [Int.cast_zero, sub_zero, add_zero] using
      hdual k extentX extentY exact hslackDual
  let data : PairedAdjacentCrossNestedOutwardArrayData
      E Edual mu muDual scheduleData padding K := {
    dualRadius := dualRadius
    dualOutward := hdual'
    index := index
    slack := slack
    chain := chain }
  refine ⟨data, ?_, ?_⟩
  · intro n j
    exact (Classical.choose_spec (hchain n)).1 j
  · intro n j
    exact (Classical.choose_spec (hchain n)).2 j


theorem PairedAdjacentCrossNestedOutwardArrayData.even_odd_local_limits
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {step : Nat -> Int}
    {scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step}
    {padding : Nat} {K : Nat -> Nat}
    (data : PairedAdjacentCrossNestedOutwardArrayData
      E Edual mu muDual scheduleData padding K)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    (forall k : Nat -> Nat, Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent 0
        ((data.chain n).extentX (2 * k n + 2)) 0
        ((data.chain n).extentY (2 * k n + 2))))
      (mu.real (E.verticalCrossingEvent
        ((data.chain n).level (2 * k n + 2)).raw.data.wideLeft
        ((data.chain n).level (2 * k n + 2)).raw.data.wideRight 0
        (((data.chain n).extentY (2 * k n + 2)) +
          (step n).toNat))))
      atTop (nhds 1)) /\
    (forall k : Nat -> Nat, Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        ((data.chain n).level (2 * k n + 1)).raw.data.wideLeft
        ((data.chain n).level (2 * k n + 1)).raw.data.wideRight 0
        ((data.chain n).extentY (2 * k n + 1))))
      (muDual.real (Edual.horizontalCrossingEvent 0
        ((data.chain n).extentX (2 * k n + 1)) 0
        ((data.chain n).extentY (2 * k n + 1))))) atTop (nhds 1)) := by
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
  constructor
  · intro k
    exact scheduleData.alignedExact_primalAdjacent_limit hFKG hTI hunique
      data.index (fun n => (data.chain n).extentX (2 * k n + 2))
      (fun n => (data.chain n).extentY (2 * k n + 2))
      (fun n => (data.chain n).level (2 * k n + 2)) hprimalSlack
  · intro k
    exact data.dualOutward data.index
      (fun n => (data.chain n).extentX (2 * k n + 1))
      (fun n => (data.chain n).extentY (2 * k n + 1))
      (fun n => (data.chain n).level (2 * k n + 1)) hdualSlack


theorem AlignedExactExtentPairedMixedBoundaryScores.shifted_matched_pair
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : D.primalEmbedding.NormalBoundaryBandFamily mu S p}
    {familyDual : D.dualEmbedding.NormalBoundaryBandFamily
      (D.dualMeasure mu) Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule D.primalEmbedding
      D.dualEmbedding family familyDual
      verticalRequirement horizontalRequirement}
    {k lowerX lowerY upperX upperY padding : Nat}
    (lower : AlignedExactExtentPairedMixedBoundaryScores
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      S Sdual p pDual family familyDual schedule k lowerX lowerY)
    (upper : AlignedExactExtentPairedMixedBoundaryScores
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      S Sdual p pDual family familyDual schedule k upperX upperY)
    (hnextX : (upperX : Int) = lower.raw.wideRightInt -
      lower.raw.wideLeftInt + 2 * padding)
    (hnextY : lowerY = upperY + 2 * padding)
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
    (hlowerX : 10 * B < lowerX) (hlowerY : 10 * B < lowerY)
    (hupperX : 10 * B < upperX) (hupperY : 10 * B < upperY) :
    mu.real (D.primalEmbedding.horizontalCrossingEvent
        0 upperX 0 upperY) +
      (D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        lower.raw.data.wideLeft lower.raw.data.wideRight 0 lowerY) <= 1 /\
    mu.real (D.primalEmbedding.verticalCrossingEvent
        lower.raw.data.wideLeft lower.raw.data.wideRight 0 lowerY) +
      (D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        0 upperX 0 upperY) <= 1 := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  constructor
  · let z : Site 2 := fun i => if i = 0 then
      padding - lower.raw.wideLeftInt else -(padding : Int)
    have hupperXR : (upperX : Real) =
        (lower.raw.wideRightInt : Real) - lower.raw.wideLeftInt +
          2 * padding := by
      exact_mod_cast hnextX
    have hlowerYR : (lowerY : Real) = upperY + 2 * padding := by
      exact_mod_cast hnextY
    have hspanX : (0 : Real) + 5 * B < upperX - 5 * B := by
      linarith
    have hspanY : -(padding : Real) + 5 * B <
        upperY + padding - 5 * B := by
      linarith
    have hbase := D.matchedCrossing_measureReal_add_le_one_of_pads
      mu hBpos hBp hBd hpadding hpadding hspanX hspanY
    have htranslated :=
      D.dualEmbedding.verticalCrossing_translate_measureReal_le
        (D.dualMeasure mu) hTIDual z lower.raw.data.wideLeft
        lower.raw.data.wideRight 0 lowerY
    have hdualLe :
        (D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
            lower.raw.data.wideLeft lower.raw.data.wideRight 0 lowerY) <=
          (D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
            padding (upperX - padding) (-padding) (upperY + padding)) := by
      calc
        _ <= (D.dualMeasure mu).real
            (D.dualEmbedding.verticalCrossingEvent
              (lower.raw.data.wideLeft + (z 0 : Real))
              (lower.raw.data.wideRight + (z 0 : Real))
              (0 + (z 1 : Real)) (lowerY + (z 1 : Real))) := htranslated
        _ = _ := by
          apply congrArg (fun event : Set (ConfigSpace (Sym2 W)) =>
            (D.dualMeasure mu).real event)
          congr 1
          all_goals simp only [z, Pi.zero_apply, if_pos, if_neg]
          · rw [lower.raw.wideLeft_eq]
            push_cast
            ring
          · rw [lower.raw.wideRight_eq]
            push_cast
            linarith [hupperXR]
          · push_cast
            ring
          · push_cast
            linarith [hlowerYR]
    simp_rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)] at hdualLe
    have hbase' :
        mu.real (D.primalEmbedding.horizontalCrossingEvent
            0 upperX 0 upperY) +
          mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
            D.dualEmbedding.verticalCrossingEvent
              padding (upperX - padding) (-padding) (upperY + padding)) <=
            1 := by
      simpa only [zero_add, neg_add_cancel, add_sub_cancel_right,
        sub_add_cancel] using hbase
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
    linarith
  · let z : Site 2 := fun i => if i = 0 then
      lower.raw.wideLeftInt - padding else (padding : Int)
    have hupperXR : (upperX : Real) =
        (lower.raw.wideRightInt : Real) - lower.raw.wideLeftInt +
          2 * padding := by
      exact_mod_cast hnextX
    have hlowerYR : (lowerY : Real) = upperY + 2 * padding := by
      exact_mod_cast hnextY
    have hwideSpan : (lowerX : Real) <=
        lower.raw.wideRightInt - lower.raw.wideLeftInt := by
      exact_mod_cast lower.raw.extentX_le_wideSpan
    have hspanX : lower.raw.data.wideLeft - padding + 5 * B <
        lower.raw.data.wideRight + padding - 5 * B := by
      rw [lower.raw.wideLeft_eq, lower.raw.wideRight_eq]
      push_cast
      have hpad0 : (0 : Real) <= padding := by positivity
      linarith
    have hspanY : (0 : Real) + 5 * B < lowerY - 5 * B := by
      linarith
    have hbase :=
      D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads
        mu hBpos hBp hBd hpadding hpadding hspanX hspanY
    have htranslated :=
      D.dualEmbedding.horizontalCrossing_translate_measureReal_le
        (D.dualMeasure mu) hTIDual z 0 upperX 0 upperY
    have hdualLe :
        (D.dualMeasure mu).real
            (D.dualEmbedding.horizontalCrossingEvent 0 upperX 0 upperY) <=
          (D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
            (lower.raw.data.wideLeft - padding)
            (lower.raw.data.wideRight + padding)
            padding (lowerY - padding)) := by
      calc
        _ <= (D.dualMeasure mu).real
            (D.dualEmbedding.horizontalCrossingEvent
              (0 + (z 0 : Real)) (upperX + (z 0 : Real))
              (0 + (z 1 : Real)) (upperY + (z 1 : Real))) := htranslated
        _ = _ := by
          apply congrArg (fun event : Set (ConfigSpace (Sym2 W)) =>
            (D.dualMeasure mu).real event)
          congr 1
          all_goals simp only [z, Pi.zero_apply, if_pos, if_neg]
          · rw [lower.raw.wideLeft_eq]
            push_cast
            ring
          · rw [lower.raw.wideRight_eq]
            push_cast
            linarith [hupperXR]
          · push_cast
            ring
          · push_cast
            linarith [hlowerYR]
    simp_rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)] at hdualLe
    have hbase' :
        mu.real (D.primalEmbedding.verticalCrossingEvent
            lower.raw.data.wideLeft lower.raw.data.wideRight 0 lowerY) +
          mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
            D.dualEmbedding.horizontalCrossingEvent
              (lower.raw.data.wideLeft - padding)
              (lower.raw.data.wideRight + padding)
              padding (lowerY - padding)) <= 1 := by
      simpa only [zero_add, add_sub_cancel_right, sub_add_cancel] using hbase
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
    linarith


theorem PairedAdjacentCrossNestedOutwardArrayData.false_of_endpoints
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {scheduleData : PairedAdjacentBoundaryBandScheduleData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) (fun _ => 0)}
    {padding : Nat} {K : Nat -> Nat}
    (data : PairedAdjacentCrossNestedOutwardArrayData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      scheduleData padding K)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
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
    (hextentX : forall n j, 10 * B < (data.chain n).extentX j)
    (hextentY : forall n j, 10 * B < (data.chain n).extentY j)
    (hverticalStart : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        ((data.chain n).level 0).raw.data.wideLeft
        ((data.chain n).level 0).raw.data.wideRight 0
        ((data.chain n).extentY 0))) atTop (nhds 1))
    (hhorizontalEnd : Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent 0
        ((data.chain n).extentX (2 * (K n + 1) + 2)) 0
        ((data.chain n).extentY (2 * (K n + 1) + 2))))
      atTop (nhds 1)) : False := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  let horizontal : Nat -> Nat -> Real := fun n j => mu.real
    (D.primalEmbedding.horizontalCrossingEvent 0
      ((data.chain n).extentX j) 0 ((data.chain n).extentY j))
  let vertical : Nat -> Nat -> Real := fun n j => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      ((data.chain n).level j).raw.data.wideLeft
      ((data.chain n).level j).raw.data.wideRight 0
      ((data.chain n).extentY j))
  let dualVertical : Nat -> Nat -> Real := fun n j =>
    (D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
      ((data.chain n).level j).raw.data.wideLeft
      ((data.chain n).level j).raw.data.wideRight 0
      ((data.chain n).extentY j))
  let dualHorizontal : Nat -> Nat -> Real := fun n j =>
    (D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent 0
      ((data.chain n).extentX j) 0 ((data.chain n).extentY j))
  obtain ⟨hprimal, hdual⟩ :=
    data.even_odd_local_limits hFKG hTI hunique
  apply shifted_crossNested_array_contradiction_of_bounded_limits
    horizontal vertical dualVertical dualHorizontal K
  · intro n j
    exact measureReal_nonneg
  · intro n j
    exact measureReal_nonneg
  · intro n j
    exact measureReal_le_one
  · intro n j
    exact measureReal_le_one
  · simpa only [vertical, mul_zero] using hverticalStart
  · simpa only [horizontal] using hhorizontalEnd
  · intro n j hj
    have hpair :=
      AlignedExactExtentPairedMixedBoundaryScores.shifted_matched_pair
      D mu ((data.chain n).level j) ((data.chain n).level (j + 1))
      ((data.chain n).nextX_eq j hj) ((data.chain n).nextY_eq j hj)
      hTIDual B hBpos hBp hBd hpadding
      (hextentX n j) (hextentY n j)
      (hextentX n (j + 1)) (hextentY n (j + 1))
    simpa only [horizontal, dualVertical] using hpair.1
  · intro n j hj
    have hpair :=
      AlignedExactExtentPairedMixedBoundaryScores.shifted_matched_pair
      D mu ((data.chain n).level j) ((data.chain n).level (j + 1))
      ((data.chain n).nextX_eq j hj) ((data.chain n).nextY_eq j hj)
      hTIDual B hBpos hBp hBd hpadding
      (hextentX n j) (hextentY n j)
      (hextentX n (j + 1)) (hextentY n (j + 1))
    simpa only [vertical, dualHorizontal] using hpair.2
  · intro k hk
    have hlim := hprimal k
    simpa only [horizontal, vertical, Int.toNat_zero, Nat.cast_zero,
      add_zero] using hlim
  · intro k hk
    simpa only [dualVertical, dualHorizontal] using hdual k


end StatMech.FK.PeriodicPlanar
