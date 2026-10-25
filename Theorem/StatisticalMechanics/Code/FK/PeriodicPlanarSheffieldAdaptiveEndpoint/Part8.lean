/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part6
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation.exists_horizontalEndpoint_rebuild
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (preparation : D.CrossNestedOutwardArrayPreparation mu)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu)) :
    exists rebuilt : D.CrossNestedOutwardArrayPreparation mu,
      Tendsto (fun n => mu.real
        (D.primalEmbedding.horizontalCrossingEvent 0
          ((rebuilt.array.chain n).extentX (2 * (n + 1) + 2)) 0
          ((rebuilt.array.chain n).extentY (2 * (n + 1) + 2))))
        atTop (nhds 1) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  obtain ⟨lower, hlower⟩ := exists_nat_gt (10 * preparation.B)
  have hthree : 3 * preparation.B < 3 * (lower : Real) := by
    linarith
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have hrow (n : Nat) :=
    exists_alignedCrossNestedPairedChain_horizontalEnd_gt
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      hFKG hTI hunique hTIDual
      (preparation.scheduleData.family n)
      (preparation.scheduleData.familyDual n)
      (preparation.scheduleData.schedule n)
      (preparation.array.index n) preparation.padding (2 * (n + 1) + 2)
      preparation.B preparation.Bpos.le preparation.primalArcBound
      lower lower hthree (hepsilon n)
  let chain : forall n, AlignedCrossNestedPairedChain
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      (P.orbitBox n) (Pdual.orbitBox n)
      (preparation.scheduleData.score n)
      (preparation.scheduleData.scoreDual n)
      (preparation.scheduleData.family n)
      (preparation.scheduleData.familyDual n)
      (preparation.scheduleData.schedule n)
      (preparation.array.index n) preparation.padding (2 * (n + 1) + 2) :=
    fun n => Classical.choose (hrow n)
  let array : PairedAdjacentCrossNestedOutwardArrayData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      preparation.scheduleData preparation.padding (fun n => n) := {
    dualRadius := preparation.array.dualRadius
    dualOutward := preparation.array.dualOutward
    index := preparation.array.index
    slack := preparation.array.slack
    chain := chain }
  have hlargeX : forall n j, 10 * preparation.B <
      (array.chain n).extentX j := by
    intro n j
    have hle : lower <= (array.chain n).extentX j :=
      (Classical.choose_spec (hrow n)).1 j
    exact hlower.trans_le (by exact_mod_cast hle)
  have hlargeY : forall n j, 10 * preparation.B <
      (array.chain n).extentY j := by
    intro n j
    have hle : lower <= (array.chain n).extentY j :=
      (Classical.choose_spec (hrow n)).2.1 j
    exact hlower.trans_le (by exact_mod_cast hle)
  let rebuilt : D.CrossNestedOutwardArrayPreparation mu := {
    B := preparation.B
    Bpos := preparation.Bpos
    primalArcBound := preparation.primalArcBound
    dualArcBound := preparation.dualArcBound
    padding := preparation.padding
    padding_ge := preparation.padding_ge
    scheduleData := preparation.scheduleData
    array := array
    extentX_large := hlargeX
    extentY_large := hlargeY }
  have hlowerLimit : Tendsto (fun n => 1 - epsilon n)
      atTop (nhds 1) := by
    have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
      simpa only [epsilon] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  refine ⟨rebuilt, tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlowerLimit tendsto_const_nhds ?_ (fun _ => measureReal_le_one)⟩
  intro n
  exact le_of_lt (Classical.choose_spec (hrow n)).2.2


theorem PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation.exists_verticalEndpoint_rebuild_at_error
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (preparation : D.CrossNestedOutwardArrayPreparation mu)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (epsilon : Nat -> Real) (hepsilon : forall n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (nhds 0)) :
    exists rebuilt : D.CrossNestedOutwardArrayPreparation mu,
      (forall n, 1 - epsilon n < mu.real
        (D.primalEmbedding.verticalCrossingEvent
          ((rebuilt.array.chain n).level 0).raw.data.wideLeft
          ((rebuilt.array.chain n).level 0).raw.data.wideRight 0
          ((rebuilt.array.chain n).extentY 0))) /\
      Tendsto (fun n => mu.real
        (D.primalEmbedding.verticalCrossingEvent
          ((rebuilt.array.chain n).level 0).raw.data.wideLeft
          ((rebuilt.array.chain n).level 0).raw.data.wideRight 0
          ((rebuilt.array.chain n).extentY 0))) atTop (nhds 1) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  obtain ⟨lower, hlower⟩ := exists_nat_gt (10 * preparation.B)
  have hthree : 3 * preparation.B < 3 * (lower : Real) := by
    linarith
  have hrow (n : Nat) :=
    exists_alignedCrossNestedPairedChain_verticalStart_gt
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      hFKG hTI hunique hTIDual
      (preparation.scheduleData.family n)
      (preparation.scheduleData.familyDual n)
      (preparation.scheduleData.schedule n)
      (preparation.array.index n) preparation.padding (2 * (n + 1) + 2)
      preparation.B preparation.Bpos.le preparation.primalArcBound
      lower lower hthree (hepsilon n)
  let chain : forall n, AlignedCrossNestedPairedChain
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      (P.orbitBox n) (Pdual.orbitBox n)
      (preparation.scheduleData.score n)
      (preparation.scheduleData.scoreDual n)
      (preparation.scheduleData.family n)
      (preparation.scheduleData.familyDual n)
      (preparation.scheduleData.schedule n)
      (preparation.array.index n) preparation.padding (2 * (n + 1) + 2) :=
    fun n => Classical.choose (hrow n)
  let array : PairedAdjacentCrossNestedOutwardArrayData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      preparation.scheduleData preparation.padding (fun n => n) := {
    dualRadius := preparation.array.dualRadius
    dualOutward := preparation.array.dualOutward
    index := preparation.array.index
    slack := preparation.array.slack
    chain := chain }
  have hlargeX : forall n j, 10 * preparation.B <
      (array.chain n).extentX j := by
    intro n j
    have hle : lower <= (array.chain n).extentX j :=
      (Classical.choose_spec (hrow n)).1 j
    exact hlower.trans_le (by exact_mod_cast hle)
  have hlargeY : forall n j, 10 * preparation.B <
      (array.chain n).extentY j := by
    intro n j
    have hle : lower <= (array.chain n).extentY j :=
      (Classical.choose_spec (hrow n)).2.1 j
    exact hlower.trans_le (by exact_mod_cast hle)
  let rebuilt : D.CrossNestedOutwardArrayPreparation mu := {
    B := preparation.B
    Bpos := preparation.Bpos
    primalArcBound := preparation.primalArcBound
    dualArcBound := preparation.dualArcBound
    padding := preparation.padding
    padding_ge := preparation.padding_ge
    scheduleData := preparation.scheduleData
    array := array
    extentX_large := hlargeX
    extentY_large := hlargeY }
  have hlowerLimit : Tendsto (fun n => 1 - epsilon n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  have hpointwise : forall n, 1 - epsilon n < mu.real
      (D.primalEmbedding.verticalCrossingEvent
        ((rebuilt.array.chain n).level 0).raw.data.wideLeft
        ((rebuilt.array.chain n).level 0).raw.data.wideRight 0
        ((rebuilt.array.chain n).extentY 0)) := fun n =>
    (Classical.choose_spec (hrow n)).2.2
  refine ⟨rebuilt, hpointwise,
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlowerLimit tendsto_const_nhds (fun n => le_of_lt (hpointwise n))
        (fun _ => measureReal_le_one)⟩


theorem PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation.exists_verticalEndpoint_rebuild
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (preparation : D.CrossNestedOutwardArrayPreparation mu)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu)) :
    exists rebuilt : D.CrossNestedOutwardArrayPreparation mu,
      Tendsto (fun n => mu.real
        (D.primalEmbedding.verticalCrossingEvent
          ((rebuilt.array.chain n).level 0).raw.data.wideLeft
          ((rebuilt.array.chain n).level 0).raw.data.wideRight 0
          ((rebuilt.array.chain n).extentY 0))) atTop (nhds 1) := by
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  obtain ⟨rebuilt, _hlower, hlimit⟩ :=
    preparation.exists_verticalEndpoint_rebuild_at_error D mu
      hFKG hTI hunique hTIDual epsilon (fun n => by
        dsimp only [epsilon]
        positivity) (by
        simpa only [epsilon] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)))
  exact ⟨rebuilt, hlimit⟩


theorem PeriodicPlanarDualPair.nonempty_crossNestedOutwardArrayPreparation
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (huniqueDual : (D.dualMeasure mu)
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
    Nonempty (D.CrossNestedOutwardArrayPreparation mu) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  obtain ⟨Bp, hBp0, hBp⟩ :=
    D.primalEmbedding.exists_edgeArc_displacement_bound
  obtain ⟨Bd, hBd0, hBd⟩ :=
    D.dualEmbedding.exists_edgeArc_displacement_bound
  let B := max Bp Bd + 1
  have hBpos : 0 < B := by
    dsimp only [B]
    have hmax0 : 0 <= max Bp Bd := hBp0.trans (le_max_left _ _)
    linarith
  have hBp' : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B := by
    intro x y hxy t i
    exact (hBp hxy t i).trans (by dsimp only [B]; linarith [le_max_left Bp Bd])
  have hBd' : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B := by
    intro x y hxy t i
    exact (hBd hxy t i).trans (by dsimp only [B]; linarith [le_max_right Bp Bd])
  obtain ⟨padding, hpaddingStrict⟩ := exists_nat_gt (4 * B)
  have hpadding : 4 * B <= (padding : Real) := hpaddingStrict.le
  obtain ⟨lower, hlower⟩ := exists_nat_gt (10 * B)
  let scheduleData := Classical.choice
    (exists_pairedAdjacentBoundaryBandScheduleData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      hFKG hTI hunique hFKGDual hTIDual huniqueDual
      (fun _ => 0) (fun _ => le_rfl))
  obtain ⟨array, hlargeX, hlargeY⟩ :=
    scheduleData.exists_crossNestedOutwardArrayData hTI hFKGDual hTIDual
      huniqueDual padding (fun n => n) (fun _ => lower) (fun _ => lower)
  exact ⟨{
    B := B
    Bpos := hBpos
    primalArcBound := hBp'
    dualArcBound := hBd'
    padding := padding
    padding_ge := hpadding
    scheduleData := scheduleData
    array := array
    extentX_large := fun n j => hlower.trans_le (by
      exact_mod_cast hlargeX n j)
    extentY_large := fun n j => hlower.trans_le (by
      exact_mod_cast hlargeY n j) }⟩


theorem PeriodicPlanarDualPair.exists_canonicalCrossNestedOutwardArrayPreparation_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcommon :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    Nonempty (D.CrossNestedOutwardArrayPreparation mu) := by
  dsimp only
  letI : IsProbabilityMeasure
      (D.dualMeasure
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V)))) :=
    inferInstance
  have hdata := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  exact D.nonempty_crossNestedOutwardArrayPreparation _
    hdata.1 hdata.2.1 hdata.2.2.2.2.1
    hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.2


end StatMech.FK.PeriodicPlanar
