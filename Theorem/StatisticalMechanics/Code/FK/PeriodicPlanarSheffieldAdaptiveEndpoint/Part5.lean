/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part4
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem AlignedCrossNestedPairedChain.extentX_eq_of_zero_eq
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k padding length : Nat}
    (first second : AlignedCrossNestedPairedChain E Edual mu muDual
      S Sdual p pDual family familyDual schedule k padding length)
    (hzero : first.extentX 0 = second.extentX 0) :
    forall j, j <= length -> first.extentX j = second.extentX j := by
  intro j hj
  induction j with
  | zero => exact hzero
  | succ j ih =>
      have hjlt : j < length := by omega
      have hfirst := first.nextX_eq j hjlt
      have hsecond := second.nextX_eq j hjlt
      rw [(first.level j).wideSpan_formula, ih (by omega)] at hfirst
      rw [(second.level j).wideSpan_formula] at hsecond
      exact_mod_cast hfirst.trans hsecond.symm


theorem AlignedCrossNestedPairedChain.extentY_eq_terminal_add
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k padding length : Nat}
    (data : AlignedCrossNestedPairedChain E Edual mu muDual
      S Sdual p pDual family familyDual schedule k padding length)
    {j : Nat} (hj : j <= length) :
    data.extentY j = data.extentY length + 2 * padding * (length - j) := by
  have hgap : j + (length - j) = length := by omega
  generalize hd : length - j = d at hgap ⊢
  induction d generalizing j with
  | zero =>
      have hjlen : j = length := by omega
      subst j
      simp
  | succ d ih =>
      have hjlt : j < length := by omega
      calc
        data.extentY j = data.extentY (j + 1) + 2 * padding :=
          data.nextY_eq j hjlt
        _ = (data.extentY length + 2 * padding * d) + 2 * padding := by
          rw [ih (j := j + 1) (by omega) (by omega) (by omega)]
        _ = data.extentY length + 2 * padding * (d + 1) := by ring


theorem AlignedCrossNestedPairedChain.extentY_eq_of_terminal_eq
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k padding length : Nat}
    (first second : AlignedCrossNestedPairedChain E Edual mu muDual
      S Sdual p pDual family familyDual schedule k padding length)
    (hterminal : first.extentY length = second.extentY length) :
    forall j, j <= length -> first.extentY j = second.extentY j := by
  intro j hj
  rw [first.extentY_eq_terminal_add hj,
    second.extentY_eq_terminal_add hj, hterminal]


theorem exists_alignedCrossNestedPairedChain_at_endpoints
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding length : Nat) :
    exists thresholdX thresholdY : Nat,
      forall (initialX terminalY : Nat),
        thresholdX <= initialX -> thresholdY <= terminalY ->
        exists data : AlignedCrossNestedPairedChain E Edual mu muDual
            S Sdual p pDual family familyDual schedule k padding length,
          data.extentX 0 = initialX /\
          data.extentY length = terminalY /\
          (forall j, initialX <= data.extentX j) /\
          forall j, terminalY <= data.extentY j := by
  obtain ⟨thresholdX, thresholdY, hthreshold⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  refine ⟨thresholdX, thresholdY, ?_⟩
  intro initialX terminalY hinitialX hterminalY
  let extentY : Nat -> Nat := fun j =>
    terminalY + 2 * padding * (length - j)
  let State (j : Nat) :=
    Sigma fun x : {x : Nat // initialX <= x} =>
      AlignedExactExtentPairedMixedBoundaryScores
        E Edual mu muDual S Sdual p pDual family familyDual schedule k x.1
          (extentY j)
  have hy (j : Nat) : thresholdY <= extentY j := by
    exact hterminalY.trans (by simp only [extentY]; omega)
  let initial : State 0 :=
    ⟨⟨initialX, le_rfl⟩, Classical.choice
      (hthreshold hinitialX (hy 0))⟩
  let nextState (j : Nat) (previous : State j) : State (j + 1) := by
    let span := previous.2.raw.wideRightInt -
      previous.2.raw.wideLeftInt
    have hspan : 0 <= span :=
      (show (0 : Int) <= previous.1.1 by omega).trans
        previous.2.raw.extentX_le_wideSpan
    let nextX := span.toNat + 2 * padding
    have hpreviousX : initialX <= previous.1.1 := previous.1.2
    have hnextX : initialX <= nextX := by
      have htoNat : previous.1.1 <= span.toNat := by
        rw [Int.le_toNat hspan]
        exact previous.2.raw.extentX_le_wideSpan
      exact hpreviousX.trans (htoNat.trans (Nat.le_add_right _ _))
    have hthresholdNext : thresholdX <= nextX :=
      hinitialX.trans hnextX
    exact ⟨⟨nextX, hnextX⟩, Classical.choice
      (hthreshold hthresholdNext (hy (j + 1)))⟩
  let state : forall j, State j := fun j =>
    Nat.rec (motive := State) initial nextState j
  let extentX : Nat -> Nat := fun j => (state j).1.1
  let level : forall j, AlignedExactExtentPairedMixedBoundaryScores
      E Edual mu muDual S Sdual p pDual family familyDual schedule k
        (extentX j) (extentY j) := fun j => (state j).2
  let data : AlignedCrossNestedPairedChain E Edual mu muDual
      S Sdual p pDual family familyDual schedule k padding length := {
    extentX := extentX
    extentY := extentY
    level := level
    nextX_eq := by
      intro j hj
      let span := (state j).2.raw.wideRightInt -
        (state j).2.raw.wideLeftInt
      have hspan : 0 <= span :=
        (show (0 : Int) <= (state j).1.1 by omega).trans
          (state j).2.raw.extentX_le_wideSpan
      change ((state (j + 1)).1.1 : Int) = span + 2 * (padding : Int)
      simp only [state, Nat.rec_add_one, nextState]
      change ((span.toNat + 2 * padding : Nat) : Int) =
        span + 2 * (padding : Int)
      push_cast
      rw [Int.toNat_of_nonneg hspan]
    nextY_eq := by
      intro j hj
      dsimp only [extentY]
      have hsub : length - j = length - (j + 1) + 1 := by omega
      rw [hsub]
      simp only [Nat.mul_add, Nat.mul_one]
      omega }
  refine ⟨data, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [data, extentY, Nat.sub_self, mul_zero, add_zero]
  · intro j
    exact (state j).1.2
  · intro j
    dsimp only [data, extentY]
    omega


theorem exists_alignedCrossNestedPairedChain_horizontalEnd_gt
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding length : Nat)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (lowerX lowerY : Nat) (hlowerX : 3 * B < 3 * (lowerX : Real))
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists data : AlignedCrossNestedPairedChain E Edual mu muDual
        S Sdual p pDual family familyDual schedule k padding length,
      (forall j, lowerX <= data.extentX j) /\
      (forall j, lowerY <= data.extentY j) /\
      1 - epsilon < mu.real (E.horizontalCrossingEvent 0
        (data.extentX length) 0 (data.extentY length)) := by
  obtain ⟨thresholdX, thresholdY, hchain⟩ :=
    exists_alignedCrossNestedPairedChain_at_endpoints
      E Edual mu muDual hTI hTIDual family familyDual schedule
        k padding length
  let initialX := max thresholdX lowerX
  let probeTerminalY := max thresholdY lowerY
  obtain ⟨probe, hprobeX, hprobeY, hprobeXLower, hprobeYLower⟩ :=
    hchain initialX probeTerminalY
      (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hterminalWidth : 3 * B <
      ((3 * (probe.extentX length : Int) : Int) : Real) := by
    have hlower : lowerX <= probe.extentX length :=
      (Nat.le_max_right _ _).trans (hprobeXLower length)
    push_cast
    have hlowerReal : (lowerX : Real) <= probe.extentX length := by
      exact_mod_cast hlower
    linarith
  obtain ⟨height, hheight, hcrossing⟩ :=
    E.exists_horizontalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique 0 B (-(probe.extentX length : Real))
        hB0 hB (3 * (probe.extentX length : Int)) hterminalWidth
        probeTerminalY hepsilon
  have hthresholdHeight : thresholdY <= height :=
    (Nat.le_max_left _ _).trans hheight
  obtain ⟨data, hdataX, hdataY, hdataXLower, hdataYLower⟩ :=
    hchain initialX height (Nat.le_max_left _ _) hthresholdHeight
  have hterminalX : probe.extentX length = data.extentX length := by
    apply probe.extentX_eq_of_zero_eq data
    · rw [hprobeX, hdataX]
    · exact le_rfl
  have hcrossing' : 1 - epsilon < mu.real
      (E.horizontalCrossingEvent 0 (probe.extentX length) 0 height) := by
    convert hcrossing using 1 <;> push_cast <;> ring
  refine ⟨data, ?_, ?_, ?_⟩
  · intro j
    exact (Nat.le_max_right _ _).trans (hdataXLower j)
  · intro j
    exact (Nat.le_max_right _ _).trans (hheight.trans (hdataYLower j))
  · rw [← hterminalX, hdataY]
    exact hcrossing'


theorem exists_alignedCrossNestedPairedChain_verticalStart_gt
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding length : Nat)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (lowerX lowerY : Nat) (hlowerY : 3 * B < 3 * (lowerY : Real))
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists data : AlignedCrossNestedPairedChain E Edual mu muDual
        S Sdual p pDual family familyDual schedule k padding length,
      (forall j, lowerX <= data.extentX j) /\
      (forall j, lowerY <= data.extentY j) /\
      1 - epsilon < mu.real (E.verticalCrossingEvent
        (data.level 0).raw.data.wideLeft
        (data.level 0).raw.data.wideRight 0 (data.extentY 0)) := by
  obtain ⟨thresholdX, thresholdY, hchain⟩ :=
    exists_alignedCrossNestedPairedChain_at_endpoints
      E Edual mu muDual hTI hTIDual family familyDual schedule
        k padding length
  let terminalY := max thresholdY lowerY
  let initialY := terminalY + 2 * padding * length
  have hinitialHeight : 3 * B <
      ((3 * (initialY : Int) : Int) : Real) := by
    have hlower : lowerY <= initialY := by
      exact (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)
    push_cast
    have hlowerReal : (lowerY : Real) <= initialY := by
      exact_mod_cast hlower
    linarith
  obtain ⟨width, hwidth, hcrossing⟩ :=
    E.exists_verticalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique 0 B (-(initialY : Real)) hB0 hB
        (3 * (initialY : Int)) hinitialHeight (max thresholdX lowerX)
          hepsilon
  have hthresholdWidth : thresholdX <= width :=
    (Nat.le_max_left _ _).trans hwidth
  obtain ⟨data, hdataX, hdataY, hdataXLower, hdataYLower⟩ :=
    hchain width terminalY hthresholdWidth (Nat.le_max_left _ _)
  have hdataInitialY : data.extentY 0 = initialY := by
    rw [data.extentY_eq_terminal_add (j := 0) (by omega), hdataY]
    simp only [initialY, Nat.sub_zero]
  have hcrossing' : 1 - epsilon < mu.real
      (E.verticalCrossingEvent 0 width 0 initialY) := by
    convert hcrossing using 1 <;> push_cast <;> ring
  have hleft : (data.level 0).raw.data.wideLeft <= (0 : Real) :=
    (data.level 0).raw.data.wideLeft_le
  have hright : (width : Real) <=
      (data.level 0).raw.data.wideRight := by
    calc
      (width : Real) = data.extentX 0 := by exact_mod_cast hdataX.symm
      _ = (data.level 0).raw.data.narrowRight := by
        exact (data.level 0).raw.narrowRight_eq.symm
      _ <= (data.level 0).raw.data.wideRight :=
        (data.level 0).raw.data.narrowRight_le
  have hmono : E.verticalCrossingEvent 0 width 0 initialY <=
      E.verticalCrossingEvent
        (data.level 0).raw.data.wideLeft
        (data.level 0).raw.data.wideRight 0 initialY :=
    E.verticalCrossingEvent_mono_horizontal hleft hright
  have hwideCrossing : 1 - epsilon < mu.real
      (E.verticalCrossingEvent
        (data.level 0).raw.data.wideLeft
        (data.level 0).raw.data.wideRight 0 initialY) :=
    hcrossing'.trans_le (measureReal_mono hmono)
  refine ⟨data, ?_, ?_, ?_⟩
  · intro j
    exact (Nat.le_max_right _ _).trans (hwidth.trans (hdataXLower j))
  · intro j
    exact (Nat.le_max_right _ _).trans (hdataYLower j)
  · have hinitialYReal : (data.extentY 0 : Real) = initialY := by
      exact_mod_cast hdataInitialY
    rw [hinitialYReal]
    exact hwideCrossing


end StatMech.FK.PeriodicPlanar
