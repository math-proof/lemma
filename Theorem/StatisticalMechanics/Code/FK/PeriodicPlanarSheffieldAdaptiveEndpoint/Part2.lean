/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlanarDualPair.EndpointBridgedRectangleArrayCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (data : D.EndpointBridgedRectangleArrayCertificate mu) : False := by
  let a : Nat -> Nat -> Real := fun n k =>
    if k = 0 then data.startA n else if k = 1 then data.lowerA n
    else if k = 2 then data.upperA n else data.endA n
  let b : Nat -> Nat -> Real := fun n k =>
    if k = 0 then data.startB n else if k = 1 then data.lowerB n
    else if k = 2 then data.upperB n else data.endB n
  let c : Nat -> Nat -> Real := fun n k =>
    if k = 0 then data.startC n else if k = 1 then data.lowerC n
    else if k = 2 then data.upperC n else data.endC n
  let d : Nat -> Nat -> Real := fun n k =>
    if k = 0 then data.startD n else if k = 1 then data.lowerD n
    else if k = 2 then data.upperD n else data.endD n
  let K : Nat -> Nat := fun _ => 2
  let primal0 : Nat -> Real := fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (data.startA n) (data.startB n)
      (data.startC n + 4 * data.B) (data.startD n - 4 * data.B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (data.lowerA n + 4 * data.B) (data.lowerB n - 4 * data.B)
      (data.lowerC n) (data.lowerD n)))
  let primal1 : Nat -> Real := fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (data.lowerA n) (data.lowerB n)
      (data.lowerC n + 4 * data.B) (data.lowerD n - 4 * data.B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (data.upperA n + 4 * data.B) (data.upperB n - 4 * data.B)
      (data.upperC n) (data.upperD n)))
  let primal2 : Nat -> Real := fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (data.upperA n) (data.upperB n)
      (data.upperC n + 4 * data.B) (data.upperD n - 4 * data.B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (data.endA n + 4 * data.B) (data.endB n - 4 * data.B)
      (data.endC n) (data.endD n)))
  have hprimalMin : Tendsto (fun n =>
      min (primal0 n) (min (primal1 n) (primal2 n))) atTop (nhds 1) := by
    simpa only [primal0, primal1, primal2, min_self] using
      data.startBridge.min (data.coreAdjacent.min data.endBridge)
  have hdual0 := D.dualMeasure_crossingMax_tendsto_one mu
    (fun n => data.startA n + 4 * data.B)
    (fun n => data.startB n - 4 * data.B) data.startC data.startD
    data.startA data.startB
    (fun n => data.startC n + 4 * data.B)
    (fun n => data.startD n - 4 * data.B) data.dualStart
  have hdual1 := D.dualMeasure_crossingMax_tendsto_one mu
    (fun n => data.lowerA n + 4 * data.B)
    (fun n => data.lowerB n - 4 * data.B) data.lowerC data.lowerD
    data.lowerA data.lowerB
    (fun n => data.lowerC n + 4 * data.B)
    (fun n => data.lowerD n - 4 * data.B) data.dualLower
  have hdual2 := D.dualMeasure_crossingMax_tendsto_one mu
    (fun n => data.upperA n + 4 * data.B)
    (fun n => data.upperB n - 4 * data.B) data.upperC data.upperD
    data.upperA data.upperB
    (fun n => data.upperC n + 4 * data.B)
    (fun n => data.upperD n - 4 * data.B) data.dualUpper
  have hdual3 := D.dualMeasure_crossingMax_tendsto_one mu
    (fun n => data.endA n + 4 * data.B)
    (fun n => data.endB n - 4 * data.B) data.endC data.endD
    data.endA data.endB
    (fun n => data.endC n + 4 * data.B)
    (fun n => data.endD n - 4 * data.B) data.dualEnd
  let dual0 : Nat -> Real := fun n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.startA n + 4 * data.B) (data.startB n - 4 * data.B)
        (data.startC n) (data.startD n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.startA n) (data.startB n)
        (data.startC n + 4 * data.B) (data.startD n - 4 * data.B)))
  let dual1 : Nat -> Real := fun n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.lowerA n + 4 * data.B) (data.lowerB n - 4 * data.B)
        (data.lowerC n) (data.lowerD n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.lowerA n) (data.lowerB n)
        (data.lowerC n + 4 * data.B) (data.lowerD n - 4 * data.B)))
  let dual2 : Nat -> Real := fun n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.upperA n + 4 * data.B) (data.upperB n - 4 * data.B)
        (data.upperC n) (data.upperD n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.upperA n) (data.upperB n)
        (data.upperC n + 4 * data.B) (data.upperD n - 4 * data.B)))
  let dual3 : Nat -> Real := fun n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.endA n + 4 * data.B) (data.endB n - 4 * data.B)
        (data.endC n) (data.endD n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.endA n) (data.endB n)
        (data.endC n + 4 * data.B) (data.endD n - 4 * data.B)))
  have hdualMin : Tendsto (fun n => min (dual0 n)
      (min (dual1 n) (min (dual2 n) (dual3 n)))) atTop (nhds 1) := by
    simpa only [dual0, dual1, dual2, dual3, min_self] using
      hdual0.min (hdual1.min (hdual2.min hdual3))
  apply PeriodicPlanarDualPair.RecursiveRectangleArrayCertificate.false D mu {
    B := data.B
    Bpos := data.Bpos
    primalArcBound := data.primalArcBound
    dualArcBound := data.dualArcBound
    a := a
    b := b
    c := c
    d := d
    K := K
    spanX := ?_
    spanY := ?_
    verticalStart := ?_
    horizontalEnd := ?_
    primalAdjacent := ?_
    dualLevels := ?_ }
  · intro n k
    by_cases hk0 : k = 0
    · simpa only [a, b, hk0, if_pos] using data.startSpanX n
    by_cases hk1 : k = 1
    · simp only [a, b, hk0, if_neg, hk1, if_pos]
      exact data.lowerSpanX n
    by_cases hk2 : k = 2
    · simp only [a, b, hk0, if_neg, hk1, hk2, if_pos]
      exact data.upperSpanX n
    · simp only [a, b, hk0, if_neg, hk1, hk2]
      exact data.endSpanX n
  · intro n k
    by_cases hk0 : k = 0
    · simpa only [c, d, hk0, if_pos] using data.startSpanY n
    by_cases hk1 : k = 1
    · simp only [c, d, hk0, if_neg, hk1, if_pos]
      exact data.lowerSpanY n
    by_cases hk2 : k = 2
    · simp only [c, d, hk0, if_neg, hk1, hk2, if_pos]
      exact data.upperSpanY n
    · simp only [c, d, hk0, if_neg, hk1, hk2]
      exact data.endSpanY n
  · simpa only [a, b, c, d, if_pos] using data.verticalStart
  · simpa [K, a, b, c, d] using data.horizontalEnd
  · intro k hk
    apply hprimalMin.squeeze tendsto_const_nhds
    · intro n
      have hcases : k n = 0 ∨ k n = 1 ∨ k n = 2 := by
        have := hk n
        dsimp only [K] at this
        omega
      rcases hcases with h0 | h1 | h2
      · simpa only [a, b, c, d, h0, if_pos, Nat.zero_add, if_false,
          one_ne_zero, primal0] using
          (min_le_left (primal0 n) (min (primal1 n) (primal2 n)))
      · have h10 : k n ≠ 0 := by omega
        simpa only [a, b, c, d, h1, h10, if_false, if_pos,
            Nat.reduceAdd, OfNat.ofNat, one_ne_zero, primal1] using
          ((min_le_right (primal0 n) (min (primal1 n) (primal2 n))).trans
            (min_le_left (primal1 n) (primal2 n)))
      · have h20 : k n ≠ 0 := by omega
        have h21 : k n ≠ 1 := by omega
        simpa only [a, b, c, d, h2, h20, h21, if_false, if_pos,
            Nat.reduceAdd, OfNat.ofNat, one_ne_zero, primal2] using
          ((min_le_right (primal0 n) (min (primal1 n) (primal2 n))).trans
            (min_le_right (primal1 n) (primal2 n)))
    · intro n
      exact max_le measureReal_le_one measureReal_le_one
  · intro k hk
    apply hdualMin.squeeze tendsto_const_nhds
    · intro n
      have hcases : k n = 0 ∨ k n = 1 ∨ k n = 2 ∨ k n = 3 := by
        have := hk n
        dsimp only [K] at this
        omega
      rcases hcases with h0 | h1 | h2 | h3
      · simpa only [a, b, c, d, h0, if_pos, dual0] using
          (min_le_left (dual0 n)
            (min (dual1 n) (min (dual2 n) (dual3 n))))
      · have h10 : k n ≠ 0 := by omega
        simpa only [a, b, c, d, h1, h10, if_false, if_pos, dual1] using
          ((min_le_right (dual0 n)
            (min (dual1 n) (min (dual2 n) (dual3 n)))).trans
              (min_le_left (dual1 n) (min (dual2 n) (dual3 n))))
      · have h20 : k n ≠ 0 := by omega
        have h21 : k n ≠ 1 := by omega
        simpa only [a, b, c, d, h2, h20, h21, if_false, if_pos, dual2] using
          ((min_le_right (dual0 n)
            (min (dual1 n) (min (dual2 n) (dual3 n)))).trans
              ((min_le_right (dual1 n) (min (dual2 n) (dual3 n))).trans
                (min_le_left (dual2 n) (dual3 n))))
      · have h30 : k n ≠ 0 := by omega
        have h31 : k n ≠ 1 := by omega
        have h32 : k n ≠ 2 := by omega
        simpa only [a, b, c, d, h3, h30, h31, h32, if_false, dual3] using
          ((min_le_right (dual0 n)
            (min (dual1 n) (min (dual2 n) (dual3 n)))).trans
              ((min_le_right (dual1 n) (min (dual2 n) (dual3 n))).trans
                (min_le_right (dual2 n) (dual3 n))))
    · intro n
      exact max_le measureReal_le_one measureReal_le_one


theorem PeriodicPlaneEmbedding.verticalEndpoint_tendsto_startBridge_of_mono
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (startA startB startC startD lowerA lowerB : Nat -> Real)
    (hlowerA : forall n, lowerA n <= startA n)
    (hlowerB : forall n, startB n <= lowerB n)
    (hvertical : Tendsto (fun n => mu.real (E.verticalCrossingEvent
      (startA n + 4 * B) (startB n - 4 * B)
      (startC n) (startD n))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (startA n) (startB n)
        (startC n + 4 * B) (startD n - 4 * B)))
      (mu.real (E.verticalCrossingEvent
        (lowerA n + 4 * B) (lowerB n - 4 * B)
        (startC n) (startD n)))) atTop (nhds 1) := by
  have hwide := E.verticalCrossing_tendsto_one_mono_horizontal mu
    (fun n => startA n + 4 * B) (fun n => startB n - 4 * B)
    startC startD (fun n => lowerA n + 4 * B)
    (fun n => lowerB n - 4 * B)
    (fun n => by linarith [hlowerA n])
    (fun n => by linarith [hlowerB n]) hvertical
  exact hwide.squeeze tendsto_const_nhds
    (fun _ => le_max_right _ _) (fun _ => max_le measureReal_le_one measureReal_le_one)


theorem PeriodicPlaneEmbedding.horizontalEndpoint_tendsto_endBridge_of_mono
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (endA endB upperC upperD endC endD : Nat -> Real)
    (hupperC : forall n, upperC n <= endC n)
    (hupperD : forall n, endD n <= upperD n)
    (hhorizontal : Tendsto (fun n => mu.real (E.horizontalCrossingEvent
      (endA n) (endB n) (endC n + 4 * B) (endD n - 4 * B)))
      atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (endA n) (endB n)
        (upperC n + 4 * B) (upperD n - 4 * B)))
      (mu.real (E.verticalCrossingEvent
        (endA n + 4 * B) (endB n - 4 * B)
        (endC n) (endD n)))) atTop (nhds 1) := by
  have htall := E.horizontalCrossing_tendsto_one_mono_vertical mu
    endA endB (fun n => endC n + 4 * B) (fun n => endD n - 4 * B)
    (fun n => upperC n + 4 * B) (fun n => upperD n - 4 * B)
    (fun n => by linarith [hupperC n])
    (fun n => by linarith [hupperD n]) hhorizontal
  exact htall.squeeze tendsto_const_nhds
    (fun _ => le_max_left _ _) (fun _ => max_le measureReal_le_one measureReal_le_one)


theorem PeriodicGraph.exists_finiteAdjacentHeights_pairMergeRadius_at_error
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Finset V) (steps : Finset Int) (cutoff : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists radius : Nat, cutoff <= radius /\
      forall step, step ∈ steps -> forall q : Fin 2 × (Fin 3 × Fin 3),
        mu.real (P.pairMergeErrorUnion template
          (template.image (P.shift (preferenceKingOffset q.2 +
            if q.1.val = 0 then 0 else verticalShift step))) radius) <
          epsilon := by
  classical
  let Branch := {step // step ∈ steps} × (Fin 2 × (Fin 3 × Fin 3))
  let neighbor : Nat -> Branch -> Finset V := fun _ branch =>
    template.image (P.shift (preferenceKingOffset branch.2.2 +
      if branch.2.1.val = 0 then 0 else verticalShift branch.1.1))
  obtain ⟨radius, hradius⟩ := P.exists_uniform_pairMergeRadius mu hunique
    (fun _ => template) neighbor
  have heventually : ∀ᶠ n : Nat in atTop,
      (1 : Real) / (n + 1) < epsilon :=
    (tendsto_order.1 tendsto_one_div_add_atTop_nhds_zero_nat).2
      epsilon hepsilon
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 heventually
  let n := max cutoff threshold
  refine ⟨radius n, (Nat.le_max_left _ _).trans (hradius n).1, ?_⟩
  intro step hstep q
  let branch : Branch := (⟨step, hstep⟩, q)
  exact ((hradius n).2 branch).trans
    (hthreshold n (Nat.le_max_right _ _))


theorem PeriodicPlaneEmbedding.exists_finiteWidth_horizontalEndpointHeight
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (widths : Finset Nat) (horizontalLeft horizontalRight : Nat -> Int)
    (y : Real) (minimumHeight : Nat)
    (hspan : forall width, width ∈ widths ->
      3 * B < horizontalRight width - horizontalLeft width)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists height : Nat, minimumHeight <= height /\
      forall width, width ∈ widths ->
        1 - epsilon < mu.real (E.horizontalCrossingEvent
          (horizontalLeft width) (horizontalRight width) y (y + height)) := by
  classical
  let Width := {width // width ∈ widths}
  have hexists (width : Width) : exists height : Nat,
      minimumHeight <= height /\
        1 - epsilon < mu.real (E.horizontalCrossingEvent
          (horizontalLeft width) (horizontalRight width) y (y + height)) := by
    let s : Real := 2 * horizontalLeft width - horizontalRight width
    let t : Int := 3 * (horizontalRight width - horizontalLeft width)
    have ht : 3 * B < t := by
      dsimp only [t]
      have hw := hspan width width.2
      push_cast
      nlinarith
    obtain ⟨height, hheight, hcrossing⟩ :=
      E.exists_horizontalCrossing_measureReal_gt_of_unique
        mu hFKG hTI hunique y B s hB0 hB t ht minimumHeight hepsilon
    refine ⟨height, hheight, ?_⟩
    convert hcrossing using 1 <;> dsimp only [s, t] <;> push_cast <;> ring
  let chosen : Width -> Nat := fun width => Classical.choose (hexists width)
  have hchosen (width : Width) := Classical.choose_spec (hexists width)
  let height := minimumHeight + ∑ width : Width, chosen width
  have hminimum : minimumHeight <= height := Nat.le_add_right _ _
  refine ⟨height, hminimum, ?_⟩
  intro width hwidth
  let indexed : Width := ⟨width, hwidth⟩
  have hchosen_le : chosen indexed <= height := by
    apply (Finset.single_le_sum
      (f := fun candidate : Width => chosen candidate)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ indexed)).trans
    exact Nat.le_add_left _ _
  have hmono := E.horizontalCrossingEvent_mono_vertical
    (a := (horizontalLeft width : Real))
    (b := (horizontalRight width : Real))
    (c' := y) (c := y) (d := y + chosen indexed) (d' := y + height)
    le_rfl (by gcongr)
  exact (hchosen indexed).2.trans_le (measureReal_mono hmono)


theorem PeriodicPlaneEmbedding.exists_finiteHeight_verticalEndpointWidth
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (heights : Finset Nat) (verticalBottom verticalTop : Nat -> Int)
    (x : Real) (minimumWidth : Nat)
    (hspan : forall height, height ∈ heights ->
      3 * B < verticalTop height - verticalBottom height)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists width : Nat, minimumWidth <= width /\
      forall height, height ∈ heights ->
        1 - epsilon < mu.real (E.verticalCrossingEvent
          x (x + width) (verticalBottom height) (verticalTop height)) := by
  classical
  let Height := {height // height ∈ heights}
  have hexists (height : Height) : exists width : Nat,
      minimumWidth <= width /\
        1 - epsilon < mu.real (E.verticalCrossingEvent
          x (x + width) (verticalBottom height) (verticalTop height)) := by
    let s : Real := 2 * verticalBottom height - verticalTop height
    let t : Int := 3 * (verticalTop height - verticalBottom height)
    have ht : 3 * B < t := by
      dsimp only [t]
      have hh := hspan height height.2
      push_cast
      nlinarith
    obtain ⟨width, hwidth, hcrossing⟩ :=
      E.exists_verticalCrossing_measureReal_gt_of_unique
        mu hFKG hTI hunique x B s hB0 hB t ht minimumWidth hepsilon
    refine ⟨width, hwidth, ?_⟩
    convert hcrossing using 1 <;> dsimp only [s, t] <;> push_cast <;> ring
  let chosen : Height -> Nat := fun height => Classical.choose (hexists height)
  have hchosen (height : Height) := Classical.choose_spec (hexists height)
  let width := minimumWidth + ∑ height : Height, chosen height
  have hminimum : minimumWidth <= width := Nat.le_add_right _ _
  refine ⟨width, hminimum, ?_⟩
  intro height hheight
  let indexed : Height := ⟨height, hheight⟩
  have hchosen_le : chosen indexed <= width := by
    apply (Finset.single_le_sum
      (f := fun candidate : Height => chosen candidate)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ indexed)).trans
    exact Nat.le_add_left _ _
  have hmono := E.verticalCrossingEvent_mono_horizontal
    (a' := x) (a := x) (b := x + chosen indexed) (b' := x + width)
    (c := (verticalBottom height : Real))
    (d := (verticalTop height : Real)) le_rfl (by gcongr)
  exact (hchosen indexed).2.trans_le (measureReal_mono hmono)


theorem PeriodicPlaneEmbedding.exists_finiteHeight_coupledEndpointWidthHeight
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (heights : Finset Nat) (verticalBottom verticalTop : Nat -> Int)
    (x y : Real) (minimumWidth minimumHeight : Nat)
    (horizontalLeft horizontalRight : Nat -> Int)
    (hverticalSpan : forall step, step ∈ heights ->
      3 * B < verticalTop step - verticalBottom step)
    (hhorizontalSpan : forall width, minimumWidth <= width ->
      3 * B < horizontalRight width - horizontalLeft width)
    {verticalEpsilon horizontalEpsilon : Real}
    (hVerticalEpsilon : 0 < verticalEpsilon)
    (hHorizontalEpsilon : 0 < horizontalEpsilon) :
    exists width height : Nat,
      minimumWidth <= width /\ minimumHeight <= height /\
      (forall step, step ∈ heights ->
        1 - verticalEpsilon < mu.real (E.verticalCrossingEvent
          x (x + width) (verticalBottom step) (verticalTop step))) /\
      1 - horizontalEpsilon < mu.real (E.horizontalCrossingEvent
        (horizontalLeft width) (horizontalRight width) y (y + height)) := by
  obtain ⟨width, hwidth, hvertical⟩ :=
    E.exists_finiteHeight_verticalEndpointWidth mu hFKG hTI hunique
      B hB0 hB heights verticalBottom verticalTop x minimumWidth
      hverticalSpan hVerticalEpsilon
  obtain ⟨height, hheight, hhorizontal⟩ :=
    E.exists_finiteWidth_horizontalEndpointHeight mu hFKG hTI hunique
      B hB0 hB {width} horizontalLeft horizontalRight y minimumHeight
      (fun candidate hcandidate => by
        simp only [Finset.mem_singleton] at hcandidate
        subst candidate
        exact hhorizontalSpan width hwidth)
      hHorizontalEpsilon
  refine ⟨width, height, hwidth, hheight, hvertical, ?_⟩
  exact hhorizontal width (Finset.mem_singleton_self width)


theorem PeriodicPlaneEmbedding.exists_finiteWidth_endpointHeight_pairMergeRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (template : Finset V) (widths : Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int)
    (y : Real) (minimumHeight cutoff : Nat)
    (hspan : forall width, width ∈ widths ->
      3 * B < horizontalRight width - horizontalLeft width)
    {endpointEpsilon mergeEpsilon : Real}
    (hEndpointEpsilon : 0 < endpointEpsilon)
    (hMergeEpsilon : 0 < mergeEpsilon) :
    exists height radius : Nat,
      minimumHeight <= height /\ cutoff <= radius /\
      (forall width, width ∈ widths ->
        1 - endpointEpsilon < mu.real (E.horizontalCrossingEvent
          (horizontalLeft width) (horizontalRight width) y (y + height))) /\
      forall step : Nat, step <= height ->
        forall q : Fin 2 × (Fin 3 × Fin 3),
          mu.real (P.pairMergeErrorUnion template
            (template.image (P.shift (preferenceKingOffset q.2 +
              if q.1.val = 0 then 0 else verticalShift step))) radius) <
            mergeEpsilon := by
  classical
  obtain ⟨height, hheight, hcrossing⟩ :=
    E.exists_finiteWidth_horizontalEndpointHeight mu hFKG hTI hunique
      B hB0 hB widths horizontalLeft horizontalRight y minimumHeight hspan
      hEndpointEpsilon
  let steps : Finset Int :=
    (Finset.range (height + 1)).image (fun step : Nat => (step : Int))
  obtain ⟨radius, hradius, hmerge⟩ :=
    P.exists_finiteAdjacentHeights_pairMergeRadius_at_error
      mu hunique template steps cutoff hMergeEpsilon
  refine ⟨height, radius, hheight, hradius, hcrossing, ?_⟩
  intro step hstep q
  apply hmerge (step : Int)
  simp only [steps, Finset.mem_image, Finset.mem_range]
  exact ⟨step, Nat.lt_succ_iff.mpr hstep, rfl⟩


end StatMech.FK.PeriodicPlanar
