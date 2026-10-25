/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part6
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem PeriodicPlanarDualPair.carriedCrossNestedArrays_succ_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hFKGDual : IsFKG (D.dualMeasure mu))
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (primal : D.primalEmbedding.CarriedCrossNestedArray mu)
    (dual : D.dualEmbedding.CarriedCrossNestedArray (D.dualMeasure mu))
    (hspanHX : forall n,
      primal.a (n + 1) + 5 * B < primal.b (n + 1) - 5 * B)
    (hspanDVY : forall n,
      dual.c n + 5 * B < dual.d n - 5 * B)
    (hspanDHX : forall n,
      dual.a n + 5 * B < dual.b n - 5 * B)
    (hspanVY : forall n,
      primal.c (n + 1) + 5 * B < primal.d (n + 1) - 5 * B)
    (hHBottom : forall n, dual.c n + 4 * B <= primal.cTall (n + 1))
    (hHTop : forall n, primal.dTall (n + 1) <= dual.d n - 4 * B)
    (hDVLeft : forall n, primal.a (n + 1) + 4 * B <= dual.aWide n)
    (hDVRight : forall n, dual.bWide n <= primal.b (n + 1) - 4 * B)
    (hVLeft : forall n, dual.a n + 4 * B <= primal.aWide (n + 1))
    (hVRight : forall n, primal.bWide (n + 1) <= dual.b n - 4 * B)
    (hDHBottom : forall n, primal.c (n + 1) + 4 * B <= dual.cTall n)
    (hDHTop : forall n, dual.dTall n <= primal.d (n + 1) - 4 * B) : False := by
  exact D.carriedCrossNestedArrays_false mu hFKG hFKGDual B hBpos hBp hBd
    (primal.tail D.primalEmbedding mu) dual
    hspanHX hspanDVY hspanDHX hspanVY
    hHBottom hHTop hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop


theorem asymmetricComplementaryEndpointLimits_false
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (H V dualV dualH : Nat -> Real)
    (hH0 : forall n, 0 <= H n) (hV0 : forall n, 0 <= V n)
    (hHdual : forall n, H n + dualV n <= 1)
    (hVdual : forall n, V n + dualH n <= 1)
    (hprimal : Tendsto (fun n => max (H n) (V n)) atTop (nhds 1))
    (hdualV : Tendsto dualV atTop (nhds 1))
    (hdualH : Tendsto dualH atTop (nhds 1)) : False := by
  have hHzero : Tendsto H atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 1 - dualV n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualV
    apply squeeze_zero hH0 (fun n => ?_)
      hupper
    linarith [hHdual n]
  have hVzero : Tendsto V atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 1 - dualH n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualH
    apply squeeze_zero hV0 (fun n => ?_)
      hupper
    linarith [hVdual n]
  have hzero : Tendsto (fun n => max (H n) (V n))
      atTop (nhds 0) := by
    simpa using hHzero.max hVzero
  have : (0 : Real) = 1 := tendsto_nhds_unique hzero hprimal
  norm_num at this


theorem PeriodicPlanarDualPair.variablePadBranchAlignedComplementary_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (branch : Nat -> Bool) (a b c d xPad yPad : Nat -> Real)
    (hxPad : forall n, 4 * B <= xPad n)
    (hyPad : forall n, 4 * B <= yPad n)
    (hspanX : forall n, a n + 5 * B < b n - 5 * B)
    (hspanY : forall n, c n + 5 * B < d n - 5 * B)
    (hprimal : Tendsto (fun n => if branch n then
      mu.real (D.primalEmbedding.verticalCrossingEvent
        (a n + xPad n) (b n - xPad n) (c n) (d n))
    else
      mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a n) (b n) (c n + yPad n) (d n - yPad n)))
      atTop (nhds 1))
    (hdual : Tendsto (fun n => if branch n then
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a n) (b n) (c n + yPad n) (d n - yPad n))
    else
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a n + xPad n) (b n - xPad n) (c n) (d n)))
      atTop (nhds 1)) : False := by
  apply branchAlignedComplementaryLimits_false branch
    (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a n) (b n) (c n + yPad n) (d n - yPad n)))
    (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent
      (a n + xPad n) (b n - xPad n) (c n) (d n)))
    (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a n + xPad n) (b n - xPad n) (c n) (d n)))
    (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a n) (b n) (c n + yPad n) (d n - yPad n)))
  · intro n
    exact D.matchedCrossing_measureReal_add_le_one_of_pads mu hBpos
      hBp hBd (hxPad n) (hyPad n) (hspanX n) (hspanY n)
  · intro n
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads
      mu hBpos hBp hBd (hxPad n) (hyPad n)
        (hspanX n) (hspanY n)
  · exact hprimal
  · exact hdual


theorem PeriodicPlanarDualPair.outwardBranchAlignedComplementary_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (branch : Nat -> Bool) (a b c d xPad yPad : Nat -> Real)
    (vLeft vRight vBottom vTop : Nat -> Real)
    (hLeft hRight hBottom hTop : Nat -> Real)
    (hvLeft : forall n, vLeft n = a n + xPad n)
    (hvRight : forall n, vRight n = b n - xPad n)
    (hvBottom : forall n, vBottom n = c n)
    (hvTop : forall n, vTop n = d n)
    (hhLeft : forall n, hLeft n = a n)
    (hhRight : forall n, hRight n = b n)
    (hhBottom : forall n, hBottom n = c n + yPad n)
    (hhTop : forall n, hTop n = d n - yPad n)
    (hxPad : forall n, 4 * B <= xPad n)
    (hyPad : forall n, 4 * B <= yPad n)
    (hspanX : forall n, a n + 5 * B < b n - 5 * B)
    (hspanY : forall n, c n + 5 * B < d n - 5 * B)
    (hprimal : Tendsto (fun n => if branch n then
      mu.real (D.primalEmbedding.verticalCrossingEvent
        (vLeft n) (vRight n) (vBottom n) (vTop n))
    else
      mu.real (D.primalEmbedding.horizontalCrossingEvent
        (hLeft n) (hRight n) (hBottom n) (hTop n)))
      atTop (nhds 1))
    (hdual : Tendsto (fun n => if branch n then
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (hLeft n) (hRight n) (hBottom n) (hTop n))
    else
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (vLeft n) (vRight n) (vBottom n) (vTop n)))
      atTop (nhds 1)) : False := by
  apply D.variablePadBranchAlignedComplementary_false mu B hBpos hBp hBd
    branch a b c d xPad yPad hxPad hyPad hspanX hspanY
  · apply hprimal.congr'
    filter_upwards [] with n
    simp only [hvLeft n, hvRight n, hvBottom n, hvTop n,
      hhLeft n, hhRight n, hhBottom n, hhTop n]
  · apply hdual.congr'
    filter_upwards [] with n
    simp only [hvLeft n, hvRight n, hvBottom n, hvTop n,
      hhLeft n, hhRight n, hhBottom n, hhTop n]


theorem tendsto_max_one_fixedBranch_subsequence
    (H V : Nat -> Real)
    (hmax : Tendsto (fun n => max (H n) (V n)) atTop (nhds 1)) :
    (exists phi : Nat -> Nat, StrictMono phi /\
      (forall n, V (phi n) <= H (phi n)) /\
      Tendsto (fun n => H (phi n)) atTop (nhds 1)) \/
    (exists phi : Nat -> Nat, StrictMono phi /\
      (forall n, H (phi n) <= V (phi n)) /\
      Tendsto (fun n => V (phi n)) atTop (nhds 1)) := by
  let p : Nat -> Prop := fun n => V n <= H n
  by_cases hp : (setOf p).Infinite
  · left
    let phi : Nat -> Nat := Nat.nth p
    have hphi : StrictMono phi := Nat.nth_strictMono hp
    refine ⟨phi, hphi, ?_, ?_⟩
    · intro n
      exact Nat.nth_mem_of_infinite hp n
    · have hsub := hmax.comp hphi.tendsto_atTop
      apply hsub.congr'
      filter_upwards [] with n
      change max (H (phi n)) (V (phi n)) = H (phi n)
      rw [max_eq_left (Nat.nth_mem_of_infinite hp n)]
  · right
    have hpFinite : (setOf p).Finite := Set.not_infinite.mp hp
    have hnotp : (setOf fun n => ¬ p n).Infinite := by
      rw [<- Set.not_finite]
      intro hfinite
      rw [<- Set.compl_setOf p] at hfinite
      have huniv : (Set.univ : Set Nat).Finite := by
        have hunion := hpFinite.union hfinite
        simpa only [Set.union_compl_self] using hunion
      exact Set.infinite_univ huniv
    let phi : Nat -> Nat := Nat.nth (fun n => ¬ p n)
    have hphi : StrictMono phi := Nat.nth_strictMono hnotp
    refine ⟨phi, hphi, ?_, ?_⟩
    · intro n
      exact le_of_not_ge (Nat.nth_mem_of_infinite hnotp n)
    · have hsub := hmax.comp hphi.tendsto_atTop
      apply hsub.congr'
      filter_upwards [] with n
      change max (H (phi n)) (V (phi n)) = V (phi n)
      rw [max_eq_right (le_of_not_ge
        (Nat.nth_mem_of_infinite hnotp n))]


theorem AlignedCrossNestedPairedSequence.false_of_primalAdjacent_and_dualMergeLimits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {p pDual : Nat -> Real}
    {family : forall n, D.primalEmbedding.NormalBoundaryBandFamily
      mu (P.orbitBox n) (p n)}
    {familyDual : forall n, D.dualEmbedding.NormalBoundaryBandFamily
      (D.dualMeasure mu) (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence D.primalEmbedding
      D.dualEmbedding mu (D.dualMeasure mu)
        p pDual family familyDual padding)
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (hpDual_le : forall n, pDual n <= 1)
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
    (hcurrentY : forall n, 10 * B < (data.triple n).currentY)
    (hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent 0
        (data.triple n).currentX 0 (data.triple n).currentY))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (data.triple n).current.raw.data.wideLeft
        (data.triple n).current.raw.data.wideRight 0
        (data.triple n).currentY))) atTop (nhds 1))
    (hmergeVertical : Tendsto (fun n => (D.dualMeasure mu).real
      (D.dualEmbedding.rectanglePairMergeErrorUnion
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        (data.triple n).previous.raw.data.dualBottomSource
        (data.triple n).previous.raw.data.dualTopSource))
      atTop (nhds 0))
    (hmergeHorizontal : Tendsto (fun n => (D.dualMeasure mu).real
      (D.dualEmbedding.rectanglePairMergeErrorUnion 0
        (data.triple n).nextX 0 (data.triple n).nextY
        (data.triple n).next.raw.data.dualLeftSource
        (data.triple n).next.raw.data.dualRightSource))
      atTop (nhds 0)) : False := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  obtain ⟨hspanX0, hspanY0, hspanX1, hspanY1⟩ :=
    data.transitionCoordinates_spans_of_current_gt B hcurrentX hcurrentY
  have hprimal' := data.primalAdjacent_transitionCoordinates hprimal
  obtain ⟨hdualV, hdualH⟩ :=
    data.dual_endpoint_transitionCoordinates_of_mergeLimits
      hFKGDual hTIDual hpDual hpDual_le hmergeVertical hmergeHorizontal
  have hdualV' : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (data.transitionA0 n + padding)
          (data.transitionB0 n - padding)
          (data.transitionC0 n) (data.transitionD0 n)))
      atTop (nhds 1) := by
    apply hdualV.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
  have hdualH' : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (data.transitionA1 n) (data.transitionB1 n)
          (data.transitionC1 n + padding)
          (data.transitionD1 n - padding)))
      atTop (nhds 1) := by
    apply hdualH.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
  apply D.variablePadComplementaryCrossNested_false mu B hBpos hBp hBd
    data.transitionA0 data.transitionB0
    data.transitionC0 data.transitionD0
    data.transitionA1 data.transitionB1
    data.transitionC1 data.transitionD1 (fun _ => (padding : Real))
    (fun _ => hpadding) hspanX0 hspanY0 hspanX1 hspanY1
  · simpa only using hprimal'
  · simpa only using hdualV'
  · simpa only using hdualH'


theorem AlignedCrossNestedPairedSequence.exists_mixedEndpointRadii_false_of_primalAdjacent
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {p pDual : Nat -> Real}
    {family : forall n, D.primalEmbedding.NormalBoundaryBandFamily
      mu (P.orbitBox n) (p n)}
    {familyDual : forall n, D.dualEmbedding.NormalBoundaryBandFamily
      (D.dualMeasure mu) (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence D.primalEmbedding
      D.dualEmbedding mu (D.dualMeasure mu)
        p pDual family familyDual padding)
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (huniqueDual : (D.dualMeasure mu)
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (hpDual : Tendsto pDual atTop (nhds 1))
    (hpDual_le : forall n, pDual n <= 1)
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
    (hcurrentY : forall n, 10 * B < (data.triple n).currentY)
    (hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent 0
        (data.triple n).currentX 0 (data.triple n).currentY))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (data.triple n).current.raw.data.wideLeft
        (data.triple n).current.raw.data.wideRight 0
        (data.triple n).currentY))) atTop (nhds 1)) :
    exists verticalRadius horizontalRadius : Nat -> Nat,
      (forall n, n <= verticalRadius n) /\
      (forall n, n <= horizontalRadius n) /\
      ((forall n,
        (Pdual.orbitBox
          (Pdual.bufferedRadius (verticalRadius n)) : Set W) <=
          D.dualEmbedding.rectVertices
            (data.triple n).previous.raw.data.wideLeft
            (data.triple n).previous.raw.data.wideRight 0
            (data.triple n).previousY) ->
       (forall n,
        (Pdual.orbitBox
          (Pdual.bufferedRadius (horizontalRadius n)) : Set W) <=
          D.dualEmbedding.rectVertices 0 (data.triple n).nextX 0
            (data.triple n).nextY) -> False) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  obtain ⟨verticalRadius, horizontalRadius, hverticalRadius,
      hhorizontalRadius, hendpoints⟩ :=
    data.exists_dual_endpoint_transitionCoordinates_of_connectorContainment
      hFKGDual hTIDual huniqueDual hpDual hpDual_le
  refine ⟨verticalRadius, horizontalRadius, hverticalRadius,
    hhorizontalRadius, ?_⟩
  intro hverticalBox hhorizontalBox
  obtain ⟨hdualV, hdualH⟩ := hendpoints hverticalBox hhorizontalBox
  obtain ⟨hspanX0, hspanY0, hspanX1, hspanY1⟩ :=
    data.transitionCoordinates_spans_of_current_gt B hcurrentX hcurrentY
  have hprimal' := data.primalAdjacent_transitionCoordinates hprimal
  have hdualV' : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (data.transitionA0 n + padding)
          (data.transitionB0 n - padding)
          (data.transitionC0 n) (data.transitionD0 n)))
      atTop (nhds 1) := by
    apply hdualV.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
  have hdualH' : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (data.transitionA1 n) (data.transitionB1 n)
          (data.transitionC1 n + padding)
          (data.transitionD1 n - padding)))
      atTop (nhds 1) := by
    apply hdualH.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
  apply D.variablePadComplementaryCrossNested_false mu B hBpos hBp hBd
    data.transitionA0 data.transitionB0
    data.transitionC0 data.transitionD0
    data.transitionA1 data.transitionB1
    data.transitionC1 data.transitionD1 (fun _ => (padding : Real))
    (fun _ => hpadding) hspanX0 hspanY0 hspanX1 hspanY1
  · simpa only using hprimal'
  · simpa only using hdualV'
  · simpa only using hdualH'


theorem PeriodicPlaneEmbedding.exists_deep_adjacentHeight_preference_crossing_branch
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (a b c d : Real) (t : Int) (ht : 0 <= t)
    {width height margin : Nat} (hwidth : 0 < width)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (source : PreferenceGridVertex width height -> Finset V)
    (bottom top left right : PreferenceGridVertex width height -> Real)
    (vertical horizontal : PreferenceGridVertex width height -> Bool)
    (hsource : forall x, (source x : Set V) <= E.rectVertices a b c d)
    (hbottomScore : forall x, bottom x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectBottomBoundaryVertices a b c d)))
    (htopScore : forall x, top x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectTopBoundaryVertices a b c d)))
    (hleftScore : forall x, left x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectLeftBoundaryVertices a b c d)))
    (hrightScore : forall x, right x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectRightBoundaryVertices a b c d)))
    (hverticalBottom : forall v, v.2.val <= margin -> vertical v = true)
    (hverticalTop : forall v, height <= v.2.val + margin ->
      vertical v = false)
    (hhorizontalLeft : forall v, v.1.val <= margin -> horizontal v = true)
    (hhorizontalRight : forall v, width <= v.1.val + margin ->
      horizontal v = false)
    (hVtrue : forall v, vertical v = true ->
      top v <= bottom v + epsilon)
    (hVfalse : forall v, vertical v = false ->
      bottom v <= top v + epsilon)
    (hHtrue : forall v, horizontal v = true ->
      right v <= left v + epsilon)
    (hHfalse : forall v, horizontal v = false ->
      left v <= right v + epsilon) :
    exists x xVertical xHorizontal : PreferenceGridVertex width height,
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) /\
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) /\
      margin <= x.1.val /\ x.1.val + margin < width /\
      margin <= x.2.val /\ x.2.val + margin < height /\
      ((1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
          bottom x + epsilon /\
        let U := (source xVertical).image (P.shift (verticalShift t))
        let Mtransfer := mu.real
          (E.rectanglePairMergeErrorUnion a b c d
            (source x) (source xVertical))
        let Mjoin := mu.real
          (E.rectanglePairMergeErrorUnion a b c (d + t) (source x) U)
        bottom x *
            (mu.real (P.setHitsInfinite (source xVertical : Set V)) *
              bottom x - Mtransfer - epsilon) - Mjoin <=
          mu.real (E.verticalCrossingEvent a b c (d + t))) \/
       (1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
          left x + epsilon /\
        left x *
            (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) *
              left x -
              mu.real (E.rectanglePairMergeErrorUnion a b c d
                (source x) (source xHorizontal)) - epsilon) -
            mu.real (E.rectanglePairMergeErrorUnion a b c d
              (source x) (source xHorizontal)) <=
          mu.real (E.horizontalCrossingEvent a b c d))) := by
  obtain ⟨x, xVertical, xHorizontal, hxV, hxH, hxVadj, hxVfalse,
      hxHadj, hxHfalse, hxLeft, hxRight, hxBottom, hxTop⟩ :=
    exists_deep_common_preference_grid_witness hwidth vertical horizontal
      hverticalBottom hverticalTop hhorizontalLeft hhorizontalRight
  have hBT := hVtrue x hxV
  have hLR := hHtrue x hxH
  rw [hbottomScore x, htopScore x] at hBT
  rw [hleftScore x, hrightScore x] at hLR
  have hpref := E.preference_max_bottom_left_add_epsilon_ge_fourthRoot
    mu hFKG a b c d (source x : Set V) epsilon hepsilon (hsource x)
      (by simpa [hbottomScore x, htopScore x] using hBT)
      (by simpa [hleftScore x, hrightScore x] using hLR)
  have hpref' :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        max (bottom x) (left x) + epsilon := by
    simpa [hbottomScore x, hleftScore x] using hpref
  refine ⟨x, xVertical, xHorizontal, hxVadj, hxHadj,
    hxLeft, hxRight, hxBottom, hxTop, ?_⟩
  by_cases hLB : left x <= bottom x
  · left
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        bottom x + epsilon := by
      simpa [max_eq_left hLB] using hpref'
    have hOpp := hVfalse xVertical hxVfalse
    rw [hbottomScore xVertical, htopScore xVertical] at hOpp
    have htransfer :=
      E.adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer
        mu hFKG hTI a b c d t ht (source x) (source xVertical) epsilon
        (by simpa [hbottomScore xVertical, htopScore xVertical] using hOpp)
    rw [<- hbottomScore x] at htransfer
    exact ⟨hroot, htransfer⟩
  · right
    have hBL : bottom x <= left x := le_of_not_ge hLB
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        left x + epsilon := by
      simpa [max_eq_right hBL] using hpref'
    have hOpp := hHfalse xHorizontal hxHfalse
    rw [hleftScore xHorizontal, hrightScore xHorizontal] at hOpp
    have htransfer := E.horizontalCrossing_ge_approxPreferredSide_transfer
      mu hFKG a b c d (source x) (source xHorizontal) epsilon
      (by simpa [hleftScore xHorizontal, hrightScore xHorizontal] using hOpp)
    rw [<- hleftScore x] at htransfer
    exact ⟨hroot, htransfer⟩


theorem PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (L R : Nat -> Finset V) (radius : Nat -> Nat)
    (z : Nat -> Site 2) (a b c d : Nat -> Real)
    (hbox : forall n,
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n) (c n) (d n))
    (hmerge : Tendsto (fun n =>
      mu.real (P.pairMergeErrorUnion (L n) (R n) (radius n)))
        atTop (nhds 0)) :
    Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
        ((L n).image (P.shift (z n)))
        ((R n).image (P.shift (z n))))) atTop (nhds 0) := by
  exact squeeze_zero (fun _ => measureReal_nonneg) (fun n =>
    E.translated_rectanglePairMergeErrorUnion_measureReal_le
      mu hTI (z n) (a n) (b n) (c n) (d n)
        (L n) (R n) (radius n) (hbox n)) hmerge


end StatMech.FK.PeriodicPlanar
