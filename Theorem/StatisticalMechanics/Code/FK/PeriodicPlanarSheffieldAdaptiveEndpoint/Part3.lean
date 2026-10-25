/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlaneEmbedding.nonempty_finiteWidthEndpointMergeRow
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
    Nonempty (E.FiniteWidthEndpointMergeRow mu template widths
      horizontalLeft horizontalRight y minimumHeight cutoff
      endpointEpsilon mergeEpsilon) := by
  obtain ⟨height, radius, hheight, hradius, hhorizontal, hmerge⟩ :=
    E.exists_finiteWidth_endpointHeight_pairMergeRadius
      mu hFKG hTI hunique B hB0 hB template widths
      horizontalLeft horizontalRight y minimumHeight cutoff hspan
      hEndpointEpsilon hMergeEpsilon
  exact ⟨{
    height := height
    radius := radius
    minimumHeight_le := hheight
    cutoff_le_radius := hradius
    horizontalEndpoint := hhorizontal
    merge := hmerge }⟩


theorem PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.nonempty_verticalEndpointExtension
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
    (endpointEpsilon mergeEpsilon : Real)
    (row : E.FiniteWidthEndpointMergeRow mu template widths
      horizontalLeft horizontalRight y minimumHeight cutoff
      endpointEpsilon mergeEpsilon)
    (verticalBottom verticalTop : Nat -> Int)
    (x : Real) (minimumWidth : Nat) (verticalEndpointEpsilon : Real)
    (hspan : forall step : Nat, step <= row.height ->
      3 * B < verticalTop step - verticalBottom step)
    (hVerticalEndpointEpsilon : 0 < verticalEndpointEpsilon) :
    Nonempty (row.VerticalEndpointExtension verticalBottom verticalTop
      x minimumWidth verticalEndpointEpsilon) := by
  let heights : Finset Nat := Finset.range (row.height + 1)
  obtain ⟨width, hwidth, hvertical⟩ :=
    E.exists_finiteHeight_verticalEndpointWidth mu hFKG hTI hunique
      B hB0 hB heights verticalBottom verticalTop x minimumWidth
      (fun step hstep => hspan step (Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hstep))) hVerticalEndpointEpsilon
  exact ⟨{
    width := width
    minimumWidth_le := hwidth
    verticalEndpoint := fun step hstep =>
      hvertical step (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hstep)) }⟩


theorem PeriodicPlaneEmbedding.exists_recursiveFiniteWidthEndpointMergeRows
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (template : Nat -> Finset V) (initialWidths : Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int) (y : Real)
    (minimumHeight cutoff : Nat -> Nat)
    (endpointEpsilon mergeEpsilon : Nat -> Real)
    (hspan : forall width,
      3 * B < horizontalRight width - horizontalLeft width)
    (hEndpointEpsilon : forall n, 0 < endpointEpsilon n)
    (hMergeEpsilon : forall n, 0 < mergeEpsilon n) :
    exists widths : Nat -> Finset Nat,
      exists rows : forall n, E.FiniteWidthEndpointMergeRow mu
        (template n) (widths n) horizontalLeft horizontalRight y
        (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n),
        widths 0 = initialWidths /\
        (forall n, widths n ⊆ widths (n + 1)) /\
        forall n, E.connectorMarginRequirement (rows n).radius ∈
          widths (n + 1) := by
  classical
  let chooseRow (n : Nat) (widths : Finset Nat) :
      E.FiniteWidthEndpointMergeRow mu (template n) widths
        horizontalLeft horizontalRight y (minimumHeight n) (cutoff n)
        (endpointEpsilon n) (mergeEpsilon n) :=
    Classical.choice (E.nonempty_finiteWidthEndpointMergeRow
      mu hFKG hTI hunique B hB0 hB (template n) widths
      horizontalLeft horizontalRight y (minimumHeight n) (cutoff n)
      (fun width _ => hspan width) (hEndpointEpsilon n) (hMergeEpsilon n))
  let widths : Nat -> Finset Nat := fun n =>
    Nat.rec initialWidths (fun n current =>
      let row := chooseRow n current
      insert (E.connectorMarginRequirement row.radius) current) n
  let rows : forall n, E.FiniteWidthEndpointMergeRow mu
      (template n) (widths n) horizontalLeft horizontalRight y
      (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n) :=
    fun n => chooseRow n (widths n)
  refine ⟨widths, rows, rfl, ?_, ?_⟩
  · intro n
    simp only [widths]
    exact Finset.subset_insert _ _
  · intro n
    simp only [widths, rows]
    exact Finset.mem_insert_self
      (E.connectorMarginRequirement (chooseRow n (widths n)).radius)
      (widths n)


theorem PeriodicPlaneEmbedding.exists_recursiveMonotoneFiniteWidthEndpointMergeRows
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (template : Nat -> Finset V) (initialWidths : Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int) (y : Real)
    (minimumHeight cutoff : Nat -> Nat)
    (endpointEpsilon mergeEpsilon : Nat -> Real)
    (hspan : forall width,
      3 * B < horizontalRight width - horizontalLeft width)
    (hEndpointEpsilon : forall n, 0 < endpointEpsilon n)
    (hMergeEpsilon : forall n, 0 < mergeEpsilon n) :
    exists state : Nat -> Finset Nat × Nat,
      exists rows : forall n, E.FiniteWidthEndpointMergeRow mu
        (template n) (state n).1 horizontalLeft horizontalRight y
        (max (minimumHeight n) (state n).2) (cutoff n)
        (endpointEpsilon n) (mergeEpsilon n),
        state 0 = (initialWidths, 0) /\
        (forall n, state (n + 1) =
          (insert (E.connectorMarginRequirement (rows n).radius) (state n).1,
            (rows n).height)) /\
        (forall n, (state n).1 ⊆ (state (n + 1)).1) /\
        (forall n, E.connectorMarginRequirement (rows n).radius ∈
          (state (n + 1)).1) /\
        forall n, (rows n).height <= (rows (n + 1)).height := by
  classical
  let chooseRow (n : Nat) (state : Finset Nat × Nat) :
      E.FiniteWidthEndpointMergeRow mu (template n) state.1
        horizontalLeft horizontalRight y (max (minimumHeight n) state.2)
        (cutoff n) (endpointEpsilon n) (mergeEpsilon n) :=
    Classical.choice (E.nonempty_finiteWidthEndpointMergeRow
      mu hFKG hTI hunique B hB0 hB (template n) state.1
      horizontalLeft horizontalRight y (max (minimumHeight n) state.2)
      (cutoff n) (fun width _ => hspan width)
      (hEndpointEpsilon n) (hMergeEpsilon n))
  let state : Nat -> Finset Nat × Nat := fun n =>
    Nat.rec (initialWidths, 0) (fun n current =>
      let row := chooseRow n current
      (insert (E.connectorMarginRequirement row.radius) current.1,
        row.height)) n
  let rows : forall n, E.FiniteWidthEndpointMergeRow mu
      (template n) (state n).1 horizontalLeft horizontalRight y
      (max (minimumHeight n) (state n).2) (cutoff n)
      (endpointEpsilon n) (mergeEpsilon n) :=
    fun n => chooseRow n (state n)
  have hstateSucc (n : Nat) : state (n + 1) =
      (insert (E.connectorMarginRequirement (rows n).radius) (state n).1,
        (rows n).height) := by
    simp only [state, rows]
  refine ⟨state, rows, rfl, hstateSucc, ?_, ?_, ?_⟩
  · intro n
    rw [hstateSucc n]
    exact Finset.subset_insert _ _
  · intro n
    rw [hstateSucc n]
    exact Finset.mem_insert_self
      (E.connectorMarginRequirement (rows n).radius) (state n).1
  · intro n
    have hminimum := (rows (n + 1)).minimumHeight_le
    have hprevious : (state (n + 1)).2 = (rows n).height := by
      rw [hstateSucc n]
    exact hprevious.symm.le.trans
      ((Nat.le_max_right _ _).trans hminimum)


theorem PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.horizontalEndpoint_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (template : Nat -> Finset V) (widths : Nat -> Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int) (y : Real)
    (minimumHeight cutoff : Nat -> Nat)
    (endpointEpsilon mergeEpsilon : Nat -> Real)
    (rows : forall n, E.FiniteWidthEndpointMergeRow mu
      (template n) (widths n) horizontalLeft horizontalRight y
      (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n))
    (width : Nat -> Nat) (hwidth : forall n, width n ∈ widths n)
    (hepsilon : Tendsto endpointEpsilon atTop (nhds 0)) :
    Tendsto (fun n => mu.real (E.horizontalCrossingEvent
      (horizontalLeft (width n)) (horizontalRight (width n))
      y (y + (rows n).height))) atTop (nhds 1) := by
  have hlower : Tendsto (fun n => 1 - endpointEpsilon n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilon
  exact hlower.squeeze tendsto_const_nhds
    (fun n => le_of_lt ((rows n).horizontalEndpoint (width n) (hwidth n)))
    (fun _ => measureReal_le_one)


theorem PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.VerticalEndpointExtension.verticalEndpoint_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (template : Nat -> Finset V) (widths : Nat -> Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int) (y : Real)
    (minimumHeight cutoff : Nat -> Nat)
    (endpointEpsilon mergeEpsilon : Nat -> Real)
    (rows : forall n, E.FiniteWidthEndpointMergeRow mu
      (template n) (widths n) horizontalLeft horizontalRight y
      (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n))
    (verticalBottom verticalTop : Nat -> Nat -> Int)
    (x : Nat -> Real) (minimumWidth : Nat -> Nat)
    (verticalEndpointEpsilon : Nat -> Real)
    (extensions : forall n, (rows n).VerticalEndpointExtension
      (verticalBottom n) (verticalTop n) (x n) (minimumWidth n)
      (verticalEndpointEpsilon n))
    (step : Nat -> Nat) (hstep : forall n, step n <= (rows n).height)
    (hepsilon : Tendsto verticalEndpointEpsilon atTop (nhds 0)) :
    Tendsto (fun n => mu.real (E.verticalCrossingEvent
      (x n) (x n + (extensions n).width)
      (verticalBottom n (step n)) (verticalTop n (step n))))
      atTop (nhds 1) := by
  have hlower : Tendsto (fun n => 1 - verticalEndpointEpsilon n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilon
  exact hlower.squeeze tendsto_const_nhds
    (fun n => le_of_lt ((extensions n).verticalEndpoint (step n) (hstep n)))
    (fun _ => measureReal_le_one)


theorem PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.merge_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (template : Nat -> Finset V) (widths : Nat -> Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int) (y : Real)
    (minimumHeight cutoff : Nat -> Nat)
    (endpointEpsilon mergeEpsilon : Nat -> Real)
    (rows : forall n, E.FiniteWidthEndpointMergeRow mu
      (template n) (widths n) horizontalLeft horizontalRight y
      (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n))
    (step : Nat -> Nat) (hstep : forall n, step n <= (rows n).height)
    (q : Nat -> Fin 2 × (Fin 3 × Fin 3))
    (hepsilon : Tendsto mergeEpsilon atTop (nhds 0)) :
    Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
      ((template n).image (P.shift (preferenceKingOffset (q n).2 +
        if (q n).1.val = 0 then 0 else verticalShift (step n))))
      (rows n).radius)) atTop (nhds 0) := by
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => le_of_lt ((rows n).merge (step n) (hstep n) (q n))) hepsilon


theorem PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.centeredAdjacent_limit_of_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (S : Nat -> Finset V) (margin M outerWidth outerHeight radius : Nat -> Nat)
    (score : Nat -> Real)
    (data : forall n, E.CommonSquareNormalBoundaryBandData
      mu (S n) (margin n) (M n) (score n))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (hMWidth : forall n, 2 * M n <= outerWidth n)
    (hMHeight : forall n, 2 * M n <= outerHeight n)
    (hwidth : forall n, 2 * margin n < outerWidth n - 2 * M n)
    (hheight : forall n, 2 * margin n < outerHeight n - 2 * M n)
    (hscore : Tendsto score atTop (nhds 1))
    (hscore_le : forall n, score n <= 1)
    (htemplateHit : Tendsto (fun n => mu.real
      (P.setHitsInfinite
        (P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight
          (data n).zBottom (data n).zTop : Set V))) atTop (nhds 1))
    (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion
        (P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight
          (data n).zBottom (data n).zTop)
        ((P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight
          (data n).zBottom (data n).zTop).image (P.shift
            (preferenceKingOffset (q n).2 +
              if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0))
    (hconnector : forall n
      (v : PreferenceGridVertex
        (outerWidth n - 2 * M n) (outerHeight n - 2 * M n)),
      margin n <= v.1.val ->
      v.1.val + margin n < outerWidth n - 2 * M n ->
      margin n <= v.2.val ->
      v.2.val + margin n < outerHeight n - 2 * M n ->
      (P.shift (preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (-(M n : Real))
            ((M n : Real) + (outerWidth n - 2 * M n : Nat))
            (-(M n : Real))
            ((M n : Real) + (outerHeight n - 2 * M n : Nat))) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        0 (outerWidth n) 0 (outerHeight n)))
      (mu.real (E.verticalCrossingEvent
        0 (outerWidth n) 0 (outerHeight n + step n))))
      atTop (nhds 1) := by
  have hcentered :=
    PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.primalAdjacent_limit_of_pairMerge
      E mu hFKG hTI S margin M (fun n => outerWidth n - 2 * M n)
      (fun n => outerHeight n - 2 * M n) radius score data step hstep
      hwidth hheight hscore hscore_le htemplateHit hmerge hconnector
  have hout := E.centeredCrossingMax_tendsto_origin mu hTI M outerWidth
    outerHeight (fun n => (step n).toNat) hMWidth hMHeight <| by
    apply hcentered.congr'
    filter_upwards [] with n
    have hstepCast : ((step n).toNat : Real) = step n := by
      exact_mod_cast Int.toNat_of_nonneg (hstep n)
    congr 3
    all_goals simp only [Nat.cast_add]
    rw [hstepCast]
  apply hout.congr'
  filter_upwards [] with n
  have hstepCast : ((step n).toNat : Real) = step n := by
    exact_mod_cast Int.toNat_of_nonneg (hstep n)
  congr 3
  rw [hstepCast]


theorem PeriodicPlanarDualPair.canonicalAdjacentHeightArray_false
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
    (width baseHeight K : Nat -> Nat)
    (hwidth : forall n, 10 * B < width n)
    (hheight : forall n, 10 * B < baseHeight n)
    (hverticalStart : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (4 * B) (width n - 4 * B) 0 (baseHeight n)))
      atTop (nhds 1))
    (hhorizontalEnd : Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        0 (width n) (4 * B)
        ((baseHeight n + (K n + 1) : Nat) - 4 * B)))
      atTop (nhds 1))
    (hprimal : forall k : Nat -> Nat, (forall n, k n < K n + 1) ->
      Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          0 (width n) (4 * B)
          ((baseHeight n + k n : Nat) - 4 * B)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (4 * B) (width n - 4 * B) 0
          (baseHeight n + (k n + 1) : Nat)))) atTop (nhds 1))
    (hdual : forall k : Nat -> Nat, (forall n, k n <= K n + 1) ->
      Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (4 * B) (width n - 4 * B) 0
            (baseHeight n + k n : Nat)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            0 (width n) (4 * B)
            ((baseHeight n + k n : Nat) - 4 * B)))) atTop (nhds 1)) :
    False := by
  let a : Nat -> Nat -> Real := fun _ _ => 0
  let b : Nat -> Nat -> Real := fun n _ => width n
  let c : Nat -> Nat -> Real := fun _ _ => 0
  let d : Nat -> Nat -> Real := fun n k => baseHeight n + k
  apply D.adjacent_rectangles_contradiction_of_bounded_max_limits mu
    hBpos hBp hBd a b c d K
  · intro n k
    dsimp only [a, b]
    have hw := hwidth n
    push_cast at hw ⊢
    linarith
  · intro n k
    dsimp only [c, d]
    have hh := hheight n
    have hk : (0 : Real) <= k := by positivity
    push_cast at hh ⊢
    linarith
  · simpa only [a, b, c, d, Nat.cast_zero, Nat.cast_add,
      zero_add, add_zero] using hverticalStart
  · simpa only [a, b, c, d, Nat.cast_zero, Nat.cast_add,
      zero_add, add_assoc] using hhorizontalEnd
  · intro k hk
    simpa only [a, b, c, d, Nat.cast_zero, Nat.cast_add,
      zero_add, add_assoc] using hprimal k hk
  · intro k hk
    simpa only [a, b, c, d, Nat.cast_zero, Nat.cast_add,
      zero_add] using hdual k hk


theorem PeriodicPlaneEmbedding.exists_mixedAdjacentHeight_approxPreferredSide_crossing_branch
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Real)
    (step : Int) (hstep : 0 <= step)
    {width height : Nat} (hwidth : 0 < width) (hheight : 0 < height)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (source : PreferenceGridVertex width height -> Finset V)
    (bottom top left right : PreferenceGridVertex width height -> Real)
    (ha : a1 <= a0) (hb : b0 <= b1)
    (hc : c0 <= c1) (hd : d1 <= d0)
    (hsource : forall x, (source x : Set V) <=
      E.rectVertices a0 b0 c1 d1)
    (hbottomScore : forall x, bottom x = mu.real
      (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V)
        (E.rectBottomBoundaryVertices a1 b1 c1 d1)))
    (htopScore : forall x, top x = mu.real
      (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V)
        (E.rectTopBoundaryVertices a1 b1 c1 d1)))
    (hleftScore : forall x, left x = mu.real
      (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V)
        (E.rectLeftBoundaryVertices a0 b0 c0 d0)))
    (hrightScore : forall x, right x = mu.real
      (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V)
        (E.rectRightBoundaryVertices a0 b0 c0 d0)))
    (hbottom : forall i : Fin (width + 1),
      top (i, 0) <= bottom (i, 0) + epsilon)
    (htop : forall i : Fin (width + 1),
      bottom (i, Fin.last height) <= top (i, Fin.last height) + epsilon)
    (hleft : forall j : Fin (height + 1),
      right (0, j) <= left (0, j) + epsilon)
    (hright : forall j : Fin (height + 1),
      left (Fin.last width, j) <= right (Fin.last width, j) + epsilon) :
    exists x xVertical xHorizontal : PreferenceGridVertex width height,
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) /\
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) /\
      ((1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
          bottom x + epsilon /\
        let shifted := (source xVertical).image
          (P.shift (verticalShift step))
        let Mtransfer := mu.real
          (E.rectanglePairMergeErrorUnion a1 b1 c1 d1
            (source x) (source xVertical))
        let Mjoin := mu.real
          (E.rectanglePairMergeErrorUnion a1 b1 c1 (d1 + step)
            (source x) shifted)
        bottom x *
            (mu.real (P.setHitsInfinite (source xVertical : Set V)) *
              bottom x - Mtransfer - epsilon) - Mjoin <=
          mu.real (E.verticalCrossingEvent a1 b1 c1 (d1 + step))) \/
       (1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
          left x + epsilon /\
        let M := mu.real
          (E.rectanglePairMergeErrorUnion a0 b0 c0 d0
            (source x) (source xHorizontal))
        left x *
            (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) *
              left x - M - epsilon) - M <=
          mu.real (E.horizontalCrossingEvent a0 b0 c0 d0))) := by
  obtain ⟨x, xVertical, xHorizontal, hxBottom, hxLeft,
      hxVertical, hxVerticalOpposite, hxHorizontal,
      hxHorizontalOpposite⟩ :=
    exists_common_weak_approximate_preference_grid_witness
      hwidth hheight epsilon hepsilon bottom top left right
      hbottom htop hleft hright
  have hpref := E.preference_mixed_max_add_epsilon_ge_fourthRoot
    mu hFKG a0 b0 c0 d0 a1 b1 c1 d1 (source x : Set V)
      epsilon hepsilon ha hb hc hd (hsource x)
      (by simpa [hbottomScore x, htopScore x] using hxBottom)
      (by simpa [hleftScore x, hrightScore x] using hxLeft)
  have hpref' :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        max (bottom x) (left x) + epsilon := by
    simpa [hbottomScore x, hleftScore x] using hpref
  refine ⟨x, xVertical, xHorizontal, hxVertical, hxHorizontal, ?_⟩
  by_cases hLB : left x <= bottom x
  · left
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        bottom x + epsilon := by
      simpa [max_eq_left hLB] using hpref'
    have htransfer :=
      E.adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer
        mu hFKG hTI a1 b1 c1 d1 step hstep
        (source x) (source xVertical) epsilon
        (by simpa [hbottomScore xVertical, htopScore xVertical] using
          hxVerticalOpposite)
    rw [<- hbottomScore x] at htransfer
    exact ⟨hroot, htransfer⟩
  · right
    have hBL : bottom x <= left x := le_of_not_ge hLB
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        left x + epsilon := by
      simpa [max_eq_right hBL] using hpref'
    have htransfer := E.horizontalCrossing_ge_approxPreferredSide_transfer
      mu hFKG a0 b0 c0 d0 (source x) (source xHorizontal) epsilon
      (by simpa [hleftScore xHorizontal, hrightScore xHorizontal] using
        hxHorizontalOpposite)
    rw [<- hleftScore x] at htransfer
    exact ⟨hroot, htransfer⟩

set_option linter.unusedVariables false in


theorem PeriodicPlaneEmbedding.mixedAdjacentHeightPreference_crossing_max_tendsto_one_of_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (radius : Nat -> Nat)
    (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0))
    (width height : Nat -> Nat)
    (hwidth : forall n, 0 < width n) (hheight : forall n, 0 < height n)
    (base : Nat -> Site 2)
    (a0 b0 c0 d0 a1 b1 c1 d1 epsilon : Nat -> Real)
    (bottom top left right : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Real)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilon0 : forall n, 0 <= epsilon n)
    (ha : forall n, a1 n <= a0 n) (hb : forall n, b0 n <= b1 n)
    (hc : forall n, c0 n <= c1 n) (hd : forall n, d1 n <= d0 n)
    (hsource : forall n (v : PreferenceGridVertex (width n) (height n)),
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V) <=
          E.rectVertices (a0 n) (b0 n) (c1 n) (d1 n))
    (hconnectorH : forall n
      (v : PreferenceGridVertex (width n) (height n)),
      (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a0 n) (b0 n) (c0 n) (d0 n))
    (hconnectorV : forall n
      (v : PreferenceGridVertex (width n) (height n)),
      (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n))
    (hbottomScore : forall n v, bottom n v = mu.real
      (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n))))
    (htopScore : forall n v, top n v = mu.real
      (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n))))
    (hleftScore : forall n v, left n v = mu.real
      (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n))))
    (hrightScore : forall n v, right n v = mu.real
      (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n))))
    (hbottom : forall n i,
      top n (i, 0) <= bottom n (i, 0) + epsilon n)
    (htop : forall n i, bottom n (i, Fin.last (height n)) <=
      top n (i, Fin.last (height n)) + epsilon n)
    (hleft : forall n j,
      right n (0, j) <= left n (0, j) + epsilon n)
    (hright : forall n j, left n (Fin.last (width n), j) <=
      right n (Fin.last (width n), j) + epsilon n) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n) (d0 n)))
      (mu.real (E.verticalCrossingEvent
        (a1 n) (b1 n) (c1 n) (d1 n + step n)))) atTop (nhds 1) := by
  classical
  let neighbor : Nat -> (Fin 2 × (Fin 3 × Fin 3)) -> Finset V :=
    fun n q => (template n).image (P.shift
      (preferenceKingOffset q.2 +
        if q.1.val = 0 then 0 else verticalShift (step n)))
  have hwitness (n : Nat) :=
    E.exists_mixedAdjacentHeight_approxPreferredSide_crossing_branch
      mu hFKG hTI
      (a0 n) (b0 n) (c0 n) (d0 n)
      (a1 n) (b1 n) (c1 n) (d1 n) (step n) (hstep n)
      (hwidth n) (hheight n) (epsilon n) (hepsilon0 n)
      (fun v => (template n).image
        (P.shift (base n + preferenceGridSite v)))
      (bottom n) (top n) (left n) (right n)
      (ha n) (hb n) (hc n) (hd n) (hsource n)
      (hbottomScore n) (htopScore n) (hleftScore n) (hrightScore n)
      (hbottom n) (htop n) (hleft n) (hright n)
  choose x xVertical xHorizontal hxVadj hxHadj hbranch using hwitness
  choose ijV hijV using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxVadj n)
  choose ijH hijH using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxHadj n)
  let source : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Finset V := fun n v =>
    (template n).image (P.shift (base n + preferenceGridSite v))
  let shiftedVerticalSource : Nat -> Finset V := fun n =>
    (source n (xVertical n)).image (P.shift (verticalShift (step n)))
  let z : Nat -> Site 2 := fun n => base n + preferenceGridSite (x n)
  have hzV (n : Nat) : z n + preferenceKingOffset (ijV n) =
      base n + preferenceGridSite (xVertical n) := by
    dsimp only [z]
    rw [hijV n]
    simp only [add_assoc]
  have hzH (n : Nat) : z n + preferenceKingOffset (ijH n) =
      base n + preferenceGridSite (xHorizontal n) := by
    dsimp only [z]
    rw [hijH n]
    simp only [add_assoc]
  have hneighbor0 (n : Nat) (ij : Fin 3 × Fin 3) :
      (neighbor n ((0 : Fin 2), ij)).image (P.shift (z n)) =
        (template n).image
          (P.shift (z n + preferenceKingOffset ij)) := by
    simp only [neighbor, Fin.isValue, Fin.val_zero, if_pos, add_zero,
      Finset.image_image]
    apply Finset.image_congr
    intro u hu
    simpa [add_comm] using
      (P.shift_add (preferenceKingOffset ij) (z n) u).symm
  have hneighbor1 (n : Nat) (ij : Fin 3 × Fin 3) :
      (neighbor n ((1 : Fin 2), ij)).image (P.shift (z n)) =
        ((template n).image
          (P.shift (z n + preferenceKingOffset ij))).image
            (P.shift (verticalShift (step n))) := by
    simp only [neighbor, Fin.isValue, Fin.val_one, one_ne_zero, if_false,
      Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift (z n)
        (P.shift (preferenceKingOffset ij + verticalShift (step n)) u) =
      P.shift (verticalShift (step n))
        (P.shift (z n + preferenceKingOffset ij) u)
    rw [<- P.shift_add, <- P.shift_add]
    congr 2
    abel
  have hrectH (n : Nat) :
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a0 n) (b0 n) (c0 n) (d0 n) :=
    hconnectorH n (x n)
  have hrectV (n : Nat) :
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n) :=
    hconnectorV n (x n)
  have hrectVTall (n : Nat) :
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n + step n) := by
    have hs : (0 : Real) <= step n := by exact_mod_cast hstep n
    exact (hrectV n).trans
      (E.rectVertices_mono le_rfl le_rfl le_rfl (by linarith))
  have hMv00 :=
    E.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
      mu hTI template (fun n => neighbor n ((0 : Fin 2), ijV n))
      radius z a1 b1 c1 d1 hrectV (by
        simpa only [neighbor] using
          hmerge (fun n => ((0 : Fin 2), ijV n)))
  have hMv10 :=
    E.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
      mu hTI template (fun n => neighbor n ((1 : Fin 2), ijV n))
      radius z a1 b1 c1 (fun n => d1 n + step n) hrectVTall (by
        simpa only [neighbor] using
          hmerge (fun n => ((1 : Fin 2), ijV n)))
  have hMh0 :=
    E.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
      mu hTI template (fun n => neighbor n ((0 : Fin 2), ijH n))
      radius z a0 b0 c0 d0 hrectH (by
        simpa only [neighbor] using
          hmerge (fun n => ((0 : Fin 2), ijH n)))
  let Mv0 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a1 n) (b1 n) (c1 n) (d1 n)
      (source n (x n)) (source n (xVertical n)))
  let Mv1 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a1 n) (b1 n) (c1 n)
      (d1 n + step n) (source n (x n)) (shiftedVerticalSource n))
  let Mv : Nat -> Real := fun n => Mv0 n + Mv1 n
  let Mh : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a0 n) (b0 n) (c0 n) (d0 n)
      (source n (x n)) (source n (xHorizontal n)))
  have hMv0 : Tendsto Mv0 atTop (nhds 0) := by
    simpa only [Mv0, source, z, hneighbor0, hzV] using hMv00
  have hMv1 : Tendsto Mv1 atTop (nhds 0) := by
    simpa only [Mv1, source, shiftedVerticalSource, z, hneighbor1, hzV]
      using hMv10
  have hMv : Tendsto Mv atTop (nhds 0) := by
    simpa only [Mv, zero_add] using hMv0.add hMv1
  have hMh : Tendsto Mh atTop (nhds 0) := by
    simpa only [Mh, source, z, hneighbor0, hzH] using hMh0
  let verticalBranch : Nat -> Prop := fun n =>
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))) <=
          bottom n (x n) + epsilon n /\
      bottom n (x n) *
          (mu.real (P.setHitsInfinite
              (source n (xVertical n) : Set V)) * bottom n (x n) -
            Mv0 n - epsilon n) - Mv1 n <=
        mu.real (E.verticalCrossingEvent
          (a1 n) (b1 n) (c1 n) (d1 n + step n))
  let A : Nat -> Real := fun n =>
    if verticalBranch n then bottom n (x n) else left n (x n)
  let Hv : Nat -> Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xVertical n) : Set V))
  let Hh : Nat -> Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xHorizontal n) : Set V))
  let Cv : Nat -> Real := fun n => mu.real
    (E.verticalCrossingEvent (a1 n) (b1 n) (c1 n) (d1 n + step n))
  let Ch : Nat -> Real := fun n => mu.real
    (E.horizontalCrossingEvent (a0 n) (b0 n) (c0 n) (d0 n))
  let root : Nat -> Real := fun n =>
    1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V))))
  have htranslatedHit (y : (n : Nat) ->
      PreferenceGridVertex (width n) (height n)) : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (source n (y n) : Set V)))
      atTop (nhds 1) := by
    apply htemplateHit.congr'
    filter_upwards with n
    have hset : ((source n (y n) : Finset V) : Set V) =
        P.shift (base n + preferenceGridSite (y n)) ''
          (template n : Set V) := by
      ext v
      simp [source]
    rw [hset, P.setHitsInfinite_translate_measureReal_eq mu hTI]
  have hroot : Tendsto root atTop (nhds 1) := by
    have hhit := htranslatedHit x
    have hmiss : Tendsto (fun n =>
        1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hhit
    simpa [root] using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  have hHv : Tendsto Hv atTop (nhds 1) := by
    simpa [Hv] using htranslatedHit xVertical
  have hHh : Tendsto Hh atTop (nhds 1) := by
    simpa [Hh] using htranslatedHit xHorizontal
  have hrootA (n : Nat) : root n <= A n + epsilon n := by
    by_cases hv : verticalBranch n
    · simpa [A, root, hv] using hv.1
    · simpa [A, root, source, shiftedVerticalSource, Mv0, Mv1, Mh,
        hv] using ((hbranch n).resolve_left hv).1
  have hAupper (n : Nat) : A n <= 1 := by
    by_cases hv : verticalBranch n
    · simp only [A, if_pos hv]
      rw [hbottomScore n (x n)]
      exact measureReal_le_one
    · simp only [A, if_neg hv]
      rw [hleftScore n (x n)]
      exact measureReal_le_one
  have hcrossingBranch (n : Nat) :
      A n * (Hv n * A n - Mv n - epsilon n) - Mv n <= Cv n \/
      A n * (Hh n * A n - Mh n - epsilon n) - Mh n <= Ch n := by
    by_cases hv : verticalBranch n
    · left
      have hraw := hv.2
      have hA0 : 0 <= bottom n (x n) := by
        rw [hbottomScore]
        exact measureReal_nonneg
      have hM0 : 0 <= Mv0 n := measureReal_nonneg
      have hM1 : 0 <= Mv1 n := measureReal_nonneg
      simp only [A, if_pos hv, Hv, Cv, Mv] at ⊢
      nlinarith
    · right
      have hraw := ((hbranch n).resolve_left hv).2
      simpa [A, Hh, Ch, Mh, source, shiftedVerticalSource, Mv0, Mv1, hv]
        using hraw
  simpa [Cv, Ch, max_comm] using
    crossing_max_tendsto_one_of_approxPreferredSide_root_branches
      root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper
      hHv hHh hMv hMh hepsilon hcrossingBranch
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)


theorem PeriodicPlaneEmbedding.exists_outward_mixed_approxPreferredSide_crossing_branch
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Real)
    (pad : Int) (hpad : 0 <= pad)
    {width height : Nat} (hwidth : 0 < width) (hheight : 0 < height)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (source : PreferenceGridVertex width height -> Finset V)
    (bottom top left right : PreferenceGridVertex width height -> Real)
    (ha : a1 <= a0) (hb : b0 <= b1)
    (hc : c0 <= c1) (hd : d1 <= d0)
    (hsource : forall x, (source x : Set V) <=
      E.rectVertices a0 b0 c1 d1)
    (hbottomScore : forall x, bottom x = mu.real
      (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V)
        (E.rectBottomBoundaryVertices a1 b1 c1 d1)))
    (htopScore : forall x, top x = mu.real
      (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V)
        (E.rectTopBoundaryVertices a1 b1 c1 d1)))
    (hleftScore : forall x, left x = mu.real
      (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V)
        (E.rectLeftBoundaryVertices a0 b0 c0 d0)))
    (hrightScore : forall x, right x = mu.real
      (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V)
        (E.rectRightBoundaryVertices a0 b0 c0 d0)))
    (hbottom : forall i : Fin (width + 1),
      top (i, 0) <= bottom (i, 0) + epsilon)
    (htop : forall i : Fin (width + 1),
      bottom (i, Fin.last height) <=
        top (i, Fin.last height) + epsilon)
    (hleft : forall j : Fin (height + 1),
      right (0, j) <= left (0, j) + epsilon)
    (hright : forall j : Fin (height + 1),
      left (Fin.last width, j) <=
        right (Fin.last width, j) + epsilon) :
    exists x xVertical xHorizontal : PreferenceGridVertex width height,
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) /\
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) /\
      ((1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
          bottom x + epsilon /\
        let Ldown := (source x).image
          (P.shift (verticalShift (-pad)))
        let Rdown := (source xVertical).image
          (P.shift (verticalShift (-pad)))
        let Rup := (source xVertical).image
          (P.shift (verticalShift pad))
        let Mtransfer := mu.real
          (E.rectanglePairMergeErrorUnion a1 b1
            (c1 - pad) (d1 - pad) Ldown Rdown)
        let Mjoin := mu.real
          (E.rectanglePairMergeErrorUnion a1 b1
            (c1 - pad) (d1 + pad) Ldown Rup)
        bottom x *
            (mu.real (P.setHitsInfinite (source xVertical : Set V)) *
              bottom x - Mtransfer - epsilon) - Mjoin <=
          mu.real (E.verticalCrossingEvent a1 b1
            (c1 - pad) (d1 + pad))) \/
       (1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
          left x + epsilon /\
        let Lleft := (source x).image
          (P.shift (horizontalShift (-pad)))
        let Rleft := (source xHorizontal).image
          (P.shift (horizontalShift (-pad)))
        let Rright := (source xHorizontal).image
          (P.shift (horizontalShift pad))
        let Mtransfer := mu.real
          (E.rectanglePairMergeErrorUnion
            (a0 - pad) (b0 - pad) c0 d0 Lleft Rleft)
        let Mjoin := mu.real
          (E.rectanglePairMergeErrorUnion
            (a0 - pad) (b0 + pad) c0 d0 Lleft Rright)
        left x *
            (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) *
              left x - Mtransfer - epsilon) - Mjoin <=
          mu.real (E.horizontalCrossingEvent
            (a0 - pad) (b0 + pad) c0 d0))) := by
  obtain ⟨x, xVertical, xHorizontal, hxBottom, hxLeft,
      hxVertical, hxVerticalOpposite, hxHorizontal,
      hxHorizontalOpposite⟩ :=
    exists_common_weak_approximate_preference_grid_witness
      hwidth hheight epsilon hepsilon bottom top left right
      hbottom htop hleft hright
  have hpref := E.preference_mixed_max_add_epsilon_ge_fourthRoot
    mu hFKG a0 b0 c0 d0 a1 b1 c1 d1 (source x : Set V)
      epsilon hepsilon ha hb hc hd (hsource x)
      (by simpa [hbottomScore x, htopScore x] using hxBottom)
      (by simpa [hleftScore x, hrightScore x] using hxLeft)
  have hpref' :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        max (bottom x) (left x) + epsilon := by
    simpa [hbottomScore x, hleftScore x] using hpref
  refine ⟨x, xVertical, xHorizontal, hxVertical, hxHorizontal, ?_⟩
  by_cases hLB : left x <= bottom x
  · left
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        bottom x + epsilon := by
      simpa [max_eq_left hLB] using hpref'
    have htransfer :=
      E.outwardVerticalCrossing_ge_approxPreferredSide_transfer
        mu hFKG hTI a1 b1 c1 d1 pad hpad
        (source x) (source xVertical) epsilon
        (by simpa [hbottomScore xVertical, htopScore xVertical] using
          hxVerticalOpposite)
    rw [<- hbottomScore x] at htransfer
    exact ⟨hroot, htransfer⟩
  · right
    have hBL : bottom x <= left x := le_of_not_ge hLB
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        left x + epsilon := by
      simpa [max_eq_right hBL] using hpref'
    have htransfer :=
      E.outwardHorizontalCrossing_ge_approxPreferredSide_transfer
        mu hFKG hTI a0 b0 c0 d0 pad hpad
        (source x) (source xHorizontal) epsilon
        (by simpa [hleftScore xHorizontal, hrightScore xHorizontal] using
          hxHorizontalOpposite)
    rw [<- hleftScore x] at htransfer
    exact ⟨hroot, htransfer⟩

set_option linter.unusedVariables false in


theorem PeriodicPlaneEmbedding.exists_uniformTemplate_outwardMixedPreference_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    exists radius : Nat -> Nat, forall
      (width height : Nat -> Nat)
      (hwidth : forall n, 0 < width n)
      (hheight : forall n, 0 < height n)
      (base : Nat -> Site 2)
      (a0 b0 c0 d0 a1 b1 c1 d1 epsilon : Nat -> Real)
      (bottom top left right : (n : Nat) ->
        PreferenceGridVertex (width n) (height n) -> Real),
      Tendsto epsilon atTop (nhds 0) ->
      (forall n, 0 <= epsilon n) ->
      (forall n, a1 n <= a0 n) ->
      (forall n, b0 n <= b1 n) ->
      (forall n, c0 n <= c1 n) ->
      (forall n, d1 n <= d0 n) ->
      (forall n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) <=
            E.rectVertices (a0 n) (b0 n) (c1 n) (d1 n)) ->
      (forall n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
            E.rectVertices (a1 n) (b1 n)
              (c1 n - pad n) (d1 n - pad n)) ->
      (forall n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
            E.rectVertices (a1 n) (b1 n)
              (c1 n - pad n) (d1 n + pad n)) ->
      (forall n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
            E.rectVertices (a0 n - pad n) (b0 n - pad n)
              (c0 n) (d0 n)) ->
      (forall n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
            E.rectVertices (a0 n - pad n) (b0 n + pad n)
              (c0 n) (d0 n)) ->
      (forall n v, bottom n v = mu.real
        (E.rectSideConnectionEvent
          (a1 n) (b1 n) (c1 n) (d1 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices
            (a1 n) (b1 n) (c1 n) (d1 n)))) ->
      (forall n v, top n v = mu.real
        (E.rectSideConnectionEvent
          (a1 n) (b1 n) (c1 n) (d1 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices
            (a1 n) (b1 n) (c1 n) (d1 n)))) ->
      (forall n v, left n v = mu.real
        (E.rectSideConnectionEvent
          (a0 n) (b0 n) (c0 n) (d0 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices
            (a0 n) (b0 n) (c0 n) (d0 n)))) ->
      (forall n v, right n v = mu.real
        (E.rectSideConnectionEvent
          (a0 n) (b0 n) (c0 n) (d0 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices
            (a0 n) (b0 n) (c0 n) (d0 n)))) ->
      (forall n i, top n (i, 0) <= bottom n (i, 0) + epsilon n) ->
      (forall n i, bottom n (i, Fin.last (height n)) <=
        top n (i, Fin.last (height n)) + epsilon n) ->
      (forall n j, right n (0, j) <= left n (0, j) + epsilon n) ->
      (forall n j, left n (Fin.last (width n), j) <=
        right n (Fin.last (width n), j) + epsilon n) ->
      exists branch : Nat -> Bool,
        Tendsto (fun n => if branch n then
          mu.real (E.verticalCrossingEvent (a1 n) (b1 n)
            (c1 n - pad n) (d1 n + pad n))
        else
          mu.real (E.horizontalCrossingEvent
            (a0 n - pad n) (b0 n + pad n) (c0 n) (d0 n)))
          atTop (nhds 1) /\
        Tendsto (fun n => max
          (mu.real (E.verticalCrossingEvent (a1 n) (b1 n)
            (c1 n - pad n) (d1 n + pad n)))
          (mu.real (E.horizontalCrossingEvent
            (a0 n - pad n) (b0 n + pad n) (c0 n) (d0 n))))
          atTop (nhds 1) := by
  classical
  let neighbor : Nat -> (Fin 3 × (Fin 3 × Fin 3)) -> Finset V := fun n q =>
    (template n).image (P.shift (preferenceKingOffset q.2 +
      if q.1.val = 0 then 0 else if q.1.val = 1 then
        verticalShift (2 * pad n) else horizontalShift (2 * pad n)))
  obtain ⟨radius, _hradius, hmerge⟩ :=
    E.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      mu hTI hunique template neighbor
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base
    a0 b0 c0 d0 a1 b1 c1 d1 epsilon bottom top left right
    hepsilon hepsilon0 ha hb hc hd hsource
    hconnectorV0 hconnectorV1 hconnectorH0 hconnectorH1
    hbottomScore htopScore hleftScore hrightScore
    hbottom htop hleft hright
  have hwitness (n : Nat) :=
    E.exists_outward_mixed_approxPreferredSide_crossing_branch
      mu hFKG hTI
      (a0 n) (b0 n) (c0 n) (d0 n)
      (a1 n) (b1 n) (c1 n) (d1 n) (pad n) (hpad n)
      (hwidth n) (hheight n) (epsilon n) (hepsilon0 n)
      (fun v => (template n).image
        (P.shift (base n + preferenceGridSite v)))
      (bottom n) (top n) (left n) (right n)
      (ha n) (hb n) (hc n) (hd n) (hsource n)
      (hbottomScore n) (htopScore n) (hleftScore n) (hrightScore n)
      (hbottom n) (htop n) (hleft n) (hright n)
  choose x xVertical xHorizontal hxVadj hxHadj hbranch using hwitness
  choose ijV hijV using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxVadj n)
  choose ijH hijH using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxHadj n)
  let source : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Finset V := fun n v =>
    (template n).image (P.shift (base n + preferenceGridSite v))
  let zV : Nat -> Site 2 := fun n =>
    base n + preferenceGridSite (x n) + verticalShift (-(pad n))
  let zH : Nat -> Site 2 := fun n =>
    base n + preferenceGridSite (x n) + horizontalShift (-(pad n))
  have hneighbor (z : Nat -> Site 2) (n : Nat)
      (q : Fin 3 × (Fin 3 × Fin 3)) :
      (neighbor n q).image (P.shift (z n)) =
        (template n).image (P.shift (z n + preferenceKingOffset q.2 +
          if q.1.val = 0 then 0 else if q.1.val = 1 then
            verticalShift (2 * pad n) else horizontalShift (2 * pad n))) := by
    simp only [neighbor, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift (z n) (P.shift (preferenceKingOffset q.2 +
        (if q.1.val = 0 then 0 else if q.1.val = 1 then
          verticalShift (2 * pad n) else horizontalShift (2 * pad n))) u) =
      P.shift (z n + preferenceKingOffset q.2 +
        (if q.1.val = 0 then 0 else if q.1.val = 1 then
          verticalShift (2 * pad n) else horizontalShift (2 * pad n))) u
    rw [<- P.shift_add]
    congr 2
    abel
  have hzV (n : Nat) :
      zV n + preferenceKingOffset (ijV n) =
        base n + preferenceGridSite (xVertical n) +
          verticalShift (-(pad n)) := by
    dsimp only [zV]
    rw [hijV n]
    abel
  have hzH (n : Nat) :
      zH n + preferenceKingOffset (ijH n) =
        base n + preferenceGridSite (xHorizontal n) +
          horizontalShift (-(pad n)) := by
    dsimp only [zH]
    rw [hijH n]
    abel
  have hMv00 := hmerge zV (fun n => ((0 : Fin 3), ijV n))
    a1 b1 (fun n => c1 n - pad n) (fun n => d1 n - pad n)
    (fun n => hconnectorV0 n (x n))
  have hMv10 := hmerge zV (fun n => ((1 : Fin 3), ijV n))
    a1 b1 (fun n => c1 n - pad n) (fun n => d1 n + pad n)
    (fun n => hconnectorV1 n (x n))
  have hMh00 := hmerge zH (fun n => ((0 : Fin 3), ijH n))
    (fun n => a0 n - pad n) (fun n => b0 n - pad n) c0 d0
    (fun n => hconnectorH0 n (x n))
  have hMh10 := hmerge zH (fun n => ((2 : Fin 3), ijH n))
    (fun n => a0 n - pad n) (fun n => b0 n + pad n) c0 d0
    (fun n => hconnectorH1 n (x n))
  let Ldown : Nat -> Finset V := fun n =>
    (source n (x n)).image (P.shift (verticalShift (-(pad n))))
  let Rdown : Nat -> Finset V := fun n =>
    (source n (xVertical n)).image (P.shift (verticalShift (-(pad n))))
  let Rup : Nat -> Finset V := fun n =>
    (source n (xVertical n)).image (P.shift (verticalShift (pad n)))
  let Lleft : Nat -> Finset V := fun n =>
    (source n (x n)).image (P.shift (horizontalShift (-(pad n))))
  let Rleft : Nat -> Finset V := fun n =>
    (source n (xHorizontal n)).image (P.shift (horizontalShift (-(pad n))))
  let Rright : Nat -> Finset V := fun n =>
    (source n (xHorizontal n)).image (P.shift (horizontalShift (pad n)))
  have htranslatedSource (n : Nat)
      (v : PreferenceGridVertex (width n) (height n)) (s : Site 2) :
      (source n v).image (P.shift s) =
        (template n).image
          (P.shift (base n + preferenceGridSite v + s)) := by
    simp only [source, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift s (P.shift (base n + preferenceGridSite v) u) =
      P.shift (base n + preferenceGridSite v + s) u
    rw [<- P.shift_add]
  have hLdown (n : Nat) :
      (template n).image (P.shift (zV n)) = Ldown n := by
    exact (htranslatedSource n (x n) (verticalShift (-(pad n)))).symm
  have hRdown (n : Nat) :
      (neighbor n ((0 : Fin 3), ijV n)).image (P.shift (zV n)) =
        Rdown n := by
    rw [hneighbor]
    simp only [Fin.val_zero, if_pos, add_zero]
    rw [hzV]
    exact (htranslatedSource n (xVertical n)
      (verticalShift (-(pad n)))).symm
  have hRup (n : Nat) :
      (neighbor n ((1 : Fin 3), ijV n)).image (P.shift (zV n)) =
        Rup n := by
    rw [hneighbor]
    simp only [Fin.val_one, one_ne_zero, if_false, if_pos]
    have hs : zV n + preferenceKingOffset (ijV n) +
        verticalShift (2 * pad n) =
      base n + preferenceGridSite (xVertical n) + verticalShift (pad n) := by
      rw [hzV]
      ext i
      fin_cases i <;> simp [verticalShift] <;> omega
    rw [hs]
    exact (htranslatedSource n (xVertical n) (verticalShift (pad n))).symm
  have hLleft (n : Nat) :
      (template n).image (P.shift (zH n)) = Lleft n := by
    exact (htranslatedSource n (x n) (horizontalShift (-(pad n)))).symm
  have hRleft (n : Nat) :
      (neighbor n ((0 : Fin 3), ijH n)).image (P.shift (zH n)) =
        Rleft n := by
    rw [hneighbor]
    simp only [Fin.val_zero, if_pos, add_zero]
    rw [hzH]
    exact (htranslatedSource n (xHorizontal n)
      (horizontalShift (-(pad n)))).symm
  have hRright (n : Nat) :
      (neighbor n ((2 : Fin 3), ijH n)).image (P.shift (zH n)) =
        Rright n := by
    rw [hneighbor]
    change (template n).image (P.shift
      (zH n + preferenceKingOffset (ijH n) +
        horizontalShift (2 * pad n))) = Rright n
    have hs : zH n + preferenceKingOffset (ijH n) +
        horizontalShift (2 * pad n) =
      base n + preferenceGridSite (xHorizontal n) +
        horizontalShift (pad n) := by
      rw [hzH]
      ext i
      fin_cases i <;> simp [horizontalShift] <;> omega
    rw [hs]
    exact (htranslatedSource n (xHorizontal n)
      (horizontalShift (pad n))).symm
  let Mv0 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a1 n) (b1 n)
      (c1 n - pad n) (d1 n - pad n) (Ldown n) (Rdown n))
  let Mv1 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a1 n) (b1 n)
      (c1 n - pad n) (d1 n + pad n) (Ldown n) (Rup n))
  let Mh0 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a0 n - pad n) (b0 n - pad n)
      (c0 n) (d0 n) (Lleft n) (Rleft n))
  let Mh1 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a0 n - pad n) (b0 n + pad n)
      (c0 n) (d0 n) (Lleft n) (Rright n))
  let Mv : Nat -> Real := fun n => Mv0 n + Mv1 n
  let Mh : Nat -> Real := fun n => Mh0 n + Mh1 n
  have hMv0 : Tendsto Mv0 atTop (nhds 0) := by
    simpa only [Mv0, hLdown, hRdown] using hMv00
  have hMv1 : Tendsto Mv1 atTop (nhds 0) := by
    simpa only [Mv1, hLdown, hRup] using hMv10
  have hMh0 : Tendsto Mh0 atTop (nhds 0) := by
    simpa only [Mh0, hLleft, hRleft] using hMh00
  have hMh1 : Tendsto Mh1 atTop (nhds 0) := by
    simpa only [Mh1, hLleft, hRright] using hMh10
  have hMv : Tendsto Mv atTop (nhds 0) := by
    simpa [Mv] using hMv0.add hMv1
  have hMh : Tendsto Mh atTop (nhds 0) := by
    simpa [Mh] using hMh0.add hMh1
  let verticalBranch : Nat -> Prop := fun n =>
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))) <=
          bottom n (x n) + epsilon n /\
      bottom n (x n) *
          (mu.real (P.setHitsInfinite
              (source n (xVertical n) : Set V)) * bottom n (x n) -
            Mv0 n - epsilon n) - Mv1 n <=
        mu.real (E.verticalCrossingEvent (a1 n) (b1 n)
          (c1 n - pad n) (d1 n + pad n))
  let A : Nat -> Real := fun n =>
    if verticalBranch n then bottom n (x n) else left n (x n)
  let Hv : Nat -> Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xVertical n) : Set V))
  let Hh : Nat -> Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xHorizontal n) : Set V))
  let Cv : Nat -> Real := fun n => mu.real
    (E.verticalCrossingEvent (a1 n) (b1 n)
      (c1 n - pad n) (d1 n + pad n))
  let Ch : Nat -> Real := fun n => mu.real
    (E.horizontalCrossingEvent
      (a0 n - pad n) (b0 n + pad n) (c0 n) (d0 n))
  let root : Nat -> Real := fun n =>
    1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V))))
  have htranslatedHit (y : (n : Nat) ->
      PreferenceGridVertex (width n) (height n)) : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (source n (y n) : Set V)))
      atTop (nhds 1) := by
    apply htemplateHit.congr'
    filter_upwards with n
    have hset : ((source n (y n) : Finset V) : Set V) =
        P.shift (base n + preferenceGridSite (y n)) ''
          (template n : Set V) := by
      ext v
      simp [source]
    rw [hset, P.setHitsInfinite_translate_measureReal_eq mu hTI]
  have hroot : Tendsto root atTop (nhds 1) := by
    have hhit := htranslatedHit x
    have hmiss : Tendsto (fun n =>
        1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hhit
    simpa [root] using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  have hHv : Tendsto Hv atTop (nhds 1) := by
    simpa [Hv] using htranslatedHit xVertical
  have hHh : Tendsto Hh atTop (nhds 1) := by
    simpa [Hh] using htranslatedHit xHorizontal
  have hrootA (n : Nat) : root n <= A n + epsilon n := by
    by_cases hv : verticalBranch n
    · simpa [A, root, hv] using hv.1
    · simpa [A, root, source, Ldown, Rdown, Rup, Lleft, Rleft,
        Rright, Mv0, Mv1, Mh0, Mh1, hv] using
        ((hbranch n).resolve_left hv).1
  have hAupper (n : Nat) : A n <= 1 := by
    by_cases hv : verticalBranch n
    · simp only [A, if_pos hv]
      rw [hbottomScore n (x n)]
      exact measureReal_le_one
    · simp only [A, if_neg hv]
      rw [hleftScore n (x n)]
      exact measureReal_le_one
  have hcrossingBranch (n : Nat) :
      A n * (Hv n * A n - Mv n - epsilon n) - Mv n <= Cv n \/
      A n * (Hh n * A n - Mh n - epsilon n) - Mh n <= Ch n := by
    by_cases hv : verticalBranch n
    · left
      have hraw := hv.2
      have hA0 : 0 <= bottom n (x n) := by
        rw [hbottomScore]
        exact measureReal_nonneg
      have hM0 : 0 <= Mv0 n := measureReal_nonneg
      have hM1 : 0 <= Mv1 n := measureReal_nonneg
      simp only [A, if_pos hv, Hv, Cv, Mv] at ⊢
      nlinarith
    · right
      have hraw := ((hbranch n).resolve_left hv).2
      have hA0 : 0 <= left n (x n) := by
        rw [hleftScore]
        exact measureReal_nonneg
      have hM0 : 0 <= Mh0 n := measureReal_nonneg
      have hM1 : 0 <= Mh1 n := measureReal_nonneg
      have hraw' :
          left n (x n) *
              (Hh n * left n (x n) - Mh0 n - epsilon n) - Mh1 n <=
            Ch n := by
        simpa [Hh, Ch, source, Ldown, Rdown, Rup, Lleft, Rleft,
          Rright, Mv0, Mv1, Mh0, Mh1] using hraw
      simp only [A, if_neg hv, Hh, Ch, Mh]
      nlinarith [hraw']
  let selectedBranch : Nat -> Bool := fun n => decide (verticalBranch n)
  have hselectedVertical (n : Nat) (hselected : selectedBranch n = true) :
      A n * (Hv n * A n - Mv n - epsilon n) - Mv n <= Cv n := by
    have hv : verticalBranch n := of_decide_eq_true hselected
    have hraw := hv.2
    have hA0 : 0 <= bottom n (x n) := by
      rw [hbottomScore]
      exact measureReal_nonneg
    have hM0 : 0 <= Mv0 n := measureReal_nonneg
    have hM1 : 0 <= Mv1 n := measureReal_nonneg
    simp only [A, if_pos hv, Hv, Cv, Mv] at ⊢
    nlinarith
  have hselectedHorizontal (n : Nat)
      (hselected : selectedBranch n = false) :
      A n * (Hh n * A n - Mh n - epsilon n) - Mh n <= Ch n := by
    have hv : ¬ verticalBranch n := of_decide_eq_false hselected
    have hraw := ((hbranch n).resolve_left hv).2
    have hA0 : 0 <= left n (x n) := by
      rw [hleftScore]
      exact measureReal_nonneg
    have hM0 : 0 <= Mh0 n := measureReal_nonneg
    have hM1 : 0 <= Mh1 n := measureReal_nonneg
    have hraw' :
        left n (x n) *
            (Hh n * left n (x n) - Mh0 n - epsilon n) - Mh1 n <=
          Ch n := by
      simpa [Hh, Ch, source, Ldown, Rdown, Rup, Lleft, Rleft,
        Rright, Mv0, Mv1, Mh0, Mh1] using hraw
    simp only [A, if_neg hv, Hh, Ch, Mh]
    nlinarith [hraw']
  have hselected :=
    crossing_selected_tendsto_one_of_approxPreferredSide_root_branches
      selectedBranch root A Hv Hh Mv Mh epsilon Cv Ch
      hroot hrootA hAupper hHv hHh hMv hMh hepsilon
      hselectedVertical hselectedHorizontal
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)
  have hmaximum :=
    crossing_max_tendsto_one_of_approxPreferredSide_root_branches
      root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper
      hHv hHh hMv hMh hepsilon hcrossingBranch
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)
  refine ⟨selectedBranch, ?_, ?_⟩
  · simpa [Cv, Ch] using hselected
  · simpa [Cv, Ch] using hmaximum


theorem PeriodicPlaneEmbedding.exists_uniformOrbitBoxOutwardMixedRadius_alignedExact_dualLimit
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual
        (Pdual.orbitBox n) (pDual n))
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
    (schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n)
      (verticalRequirement n) (horizontalRequirement n))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (hpDual_le : forall n, pDual n <= 1)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    exists radius : Nat -> Nat,
      forall (k extentX extentY : Nat -> Nat)
        (data : forall n, AlignedExactExtentPairedMixedBoundaryScores
          E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
          (p n) (pDual n) (family n) (familyDual n) (schedule n)
          (k n) (extentX n) (extentY n)),
        (forall n, PairedAlignedConnectorSlack E Edual
          (family n) (familyDual n) (schedule n)
          (max (radius n) n) (k n)) ->
        Tendsto (fun n => max
          (muDual.real (Edual.verticalCrossingEvent
            (data n).raw.data.wideLeft (data n).raw.data.wideRight
            (0 - (pad n : Real)) ((extentY n : Real) + pad n)))
          (muDual.real (Edual.horizontalCrossingEvent
            (0 - (pad n : Real)) ((extentX n : Real) + pad n)
            0 (extentY n)))) atTop (nhds 1) := by
  let template : Nat -> Finset W := fun n => Pdual.orbitBox n
  have hexists :
      muDual {eta | Pdual.HasInfiniteCluster eta} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- huniqueDual]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      muDual.real (Pdual.setHitsInfinite (template n : Set W)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      Pdual.orbitBoxHitsInfinite_real_tendsto_one muDual hexists
  obtain ⟨radius, hcross⟩ :=
    Edual.exists_uniformTemplate_outwardMixedPreference_crossing_max_tendsto_one
      muDual hFKGDual hTIDual huniqueDual template htemplateHit pad hpad
  refine ⟨radius, ?_⟩
  intro k extentX extentY data slack
  let epsilon : Nat -> Real := fun n => 1 - pDual n
  let bottom : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.widthDual)
        ((data n).raw.data.heightDual) -> Real := fun n v =>
    muDual.real (Edual.rectSideConnectionEvent
      (data n).raw.data.wideLeft (data n).raw.data.wideRight
      0 (extentY n)
      ((template n).image
        (Pdual.shift ((data n).raw.data.baseDual + preferenceGridSite v)) :
          Set W)
      (Edual.rectBottomBoundaryVertices
        (data n).raw.data.wideLeft (data n).raw.data.wideRight
        0 (extentY n)))
  let top : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.widthDual)
        ((data n).raw.data.heightDual) -> Real := fun n v =>
    muDual.real (Edual.rectSideConnectionEvent
      (data n).raw.data.wideLeft (data n).raw.data.wideRight
      0 (extentY n)
      ((template n).image
        (Pdual.shift ((data n).raw.data.baseDual + preferenceGridSite v)) :
          Set W)
      (Edual.rectTopBoundaryVertices
        (data n).raw.data.wideLeft (data n).raw.data.wideRight
        0 (extentY n)))
  let left : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.widthDual)
        ((data n).raw.data.heightDual) -> Real := fun n v =>
    muDual.real (Edual.rectSideConnectionEvent
      0 (extentX n) 0 (extentY n)
      ((template n).image
        (Pdual.shift ((data n).raw.data.baseDual + preferenceGridSite v)) :
          Set W)
      (Edual.rectLeftBoundaryVertices 0 (extentX n) 0 (extentY n)))
  let right : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.widthDual)
        ((data n).raw.data.heightDual) -> Real := fun n v =>
    muDual.real (Edual.rectSideConnectionEvent
      0 (extentX n) 0 (extentY n)
      ((template n).image
        (Pdual.shift ((data n).raw.data.baseDual + preferenceGridSite v)) :
          Set W)
      (Edual.rectRightBoundaryVertices 0 (extentX n) 0 (extentY n)))
  suffices hresult : exists branch : Nat -> Bool,
      Tendsto (fun n => if branch n then
        muDual.real (Edual.verticalCrossingEvent
          (data n).raw.data.wideLeft (data n).raw.data.wideRight
          (0 - (pad n : Real)) ((extentY n : Real) + pad n))
      else
        muDual.real (Edual.horizontalCrossingEvent
          (0 - (pad n : Real)) ((extentX n : Real) + pad n)
          0 (extentY n))) atTop (nhds 1) /\
      Tendsto (fun n => max
        (muDual.real (Edual.verticalCrossingEvent
          (data n).raw.data.wideLeft (data n).raw.data.wideRight
          (0 - (pad n : Real)) ((extentY n : Real) + pad n)))
        (muDual.real (Edual.horizontalCrossingEvent
          (0 - (pad n : Real)) ((extentX n : Real) + pad n)
          0 (extentY n)))) atTop (nhds 1) by
    obtain ⟨_branch, _hselected, hmaximum⟩ := hresult
    exact hmaximum
  apply hcross
      (fun n => (data n).raw.data.widthDual)
      (fun n => (data n).raw.data.heightDual)
      (fun n => (data n).raw.data.widthDual_pos)
      (fun n => (data n).raw.data.heightDual_pos)
      (fun n => (data n).raw.data.baseDual)
      (fun _ => 0) (fun n => (extentX n : Real))
      (fun _ => 0) (fun n => (extentY n : Real))
      (fun n => (data n).raw.data.wideLeft)
      (fun n => (data n).raw.data.wideRight)
      (fun _ => 0) (fun n => (extentY n : Real))
      epsilon bottom top left right
  · simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hpDual
  · exact fun n => sub_nonneg.mpr (hpDual_le n)
  · intro n
    exact (data n).raw.data.wideLeft_le
  · intro n
    simpa [(data n).raw.narrowRight_eq] using
      (data n).raw.data.narrowRight_le
  · intro n
    exact le_rfl
  · intro n
    exact le_rfl
  · intro n gridVertex vertex hvertex
    apply (data n).dualConnector_subset_narrow (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := by
      simpa only [template, Finset.mem_coe, Finset.mem_image] using hvertex
    refine ⟨sourceVertex, Pdual.orbitBox_mono ?_ hsourceVertex, rfl⟩
    exact (Nat.le_max_right (radius n) n).trans
      (Pdual.id_le_bufferedRadius (max (radius n) n))
  · intro n gridVertex vertex hvertex
    obtain ⟨u, hu, rfl⟩ := hvertex
    have hu' : u ∈ (Pdual.orbitBox
        (Pdual.bufferedRadius (max (radius n) n)) : Set W) :=
      Pdual.orbitBox_mono
        (Pdual.bufferedRadius_strictMono.monotone (Nat.le_max_left _ _)) hu
    have hcore0 := (data n).dualConnector_subset_wide
      (slack n) gridVertex ⟨u, hu', rfl⟩
    have hcore : Pdual.shift
        ((data n).raw.data.baseDual + preferenceGridSite gridVertex) u ∈
        Edual.rectVertices (data n).raw.data.wideLeft
          (data n).raw.data.wideRight 0 (extentY n) := by
      simpa [(data n).raw.shortTop_eq] using hcore0
    rw [show (data n).raw.data.baseDual + preferenceGridSite gridVertex +
        verticalShift (-(pad n)) =
      ((data n).raw.data.baseDual + preferenceGridSite gridVertex) +
        verticalShift (-(pad n)) by abel, Pdual.shift_add]
    have hshift := (Edual.shift_mem_rectVertices
      (verticalShift (-(pad n)))
      (data n).raw.data.wideLeft (data n).raw.data.wideRight
      0 (extentY n) _).2 hcore
    simpa [verticalShift] using hshift
  · intro n gridVertex vertex hvertex
    obtain ⟨u, hu, rfl⟩ := hvertex
    have hu' : u ∈ (Pdual.orbitBox
        (Pdual.bufferedRadius (max (radius n) n)) : Set W) :=
      Pdual.orbitBox_mono
        (Pdual.bufferedRadius_strictMono.monotone (Nat.le_max_left _ _)) hu
    have hcore0 := (data n).dualConnector_subset_wide
      (slack n) gridVertex ⟨u, hu', rfl⟩
    have hcore : Pdual.shift
        ((data n).raw.data.baseDual + preferenceGridSite gridVertex) u ∈
        Edual.rectVertices (data n).raw.data.wideLeft
          (data n).raw.data.wideRight 0 (extentY n) := by
      simpa [(data n).raw.shortTop_eq] using hcore0
    rw [show (data n).raw.data.baseDual + preferenceGridSite gridVertex +
        verticalShift (-(pad n)) =
      ((data n).raw.data.baseDual + preferenceGridSite gridVertex) +
        verticalShift (-(pad n)) by abel, Pdual.shift_add]
    have hshift := (Edual.shift_mem_rectVertices
      (verticalShift (-(pad n)))
      (data n).raw.data.wideLeft (data n).raw.data.wideRight
      0 (extentY n) _).2 hcore
    have hshift' : Pdual.shift (verticalShift (-(pad n)))
        (Pdual.shift
          ((data n).raw.data.baseDual + preferenceGridSite gridVertex) u) ∈
        Edual.rectVertices (data n).raw.data.wideLeft
          (data n).raw.data.wideRight (0 - (pad n : Real))
          ((extentY n : Real) - pad n) := by
      simpa [verticalShift] using hshift
    apply Edual.rectVertices_mono le_rfl le_rfl le_rfl _ hshift'
    have hp : (0 : Real) <= pad n := by exact_mod_cast hpad n
    push_cast
    linarith
  · intro n gridVertex vertex hvertex
    obtain ⟨u, hu, rfl⟩ := hvertex
    have hu' : u ∈ (Pdual.orbitBox
        (Pdual.bufferedRadius (max (radius n) n)) : Set W) :=
      Pdual.orbitBox_mono
        (Pdual.bufferedRadius_strictMono.monotone (Nat.le_max_left _ _)) hu
    have hcore0 := (data n).dualConnector_subset_narrow
      (slack n) gridVertex ⟨u, hu', rfl⟩
    have hcore : Pdual.shift
        ((data n).raw.data.baseDual + preferenceGridSite gridVertex) u ∈
        Edual.rectVertices 0 (extentX n) 0 (extentY n) := by
      simpa [(data n).raw.narrowRight_eq, (data n).raw.tallTop_eq]
        using hcore0
    rw [show (data n).raw.data.baseDual + preferenceGridSite gridVertex +
        horizontalShift (-(pad n)) =
      ((data n).raw.data.baseDual + preferenceGridSite gridVertex) +
        horizontalShift (-(pad n)) by abel, Pdual.shift_add]
    have hshift := (Edual.shift_mem_rectVertices
      (horizontalShift (-(pad n))) 0 (extentX n) 0 (extentY n) _).2 hcore
    simpa [horizontalShift] using hshift
  · intro n gridVertex vertex hvertex
    obtain ⟨u, hu, rfl⟩ := hvertex
    have hu' : u ∈ (Pdual.orbitBox
        (Pdual.bufferedRadius (max (radius n) n)) : Set W) :=
      Pdual.orbitBox_mono
        (Pdual.bufferedRadius_strictMono.monotone (Nat.le_max_left _ _)) hu
    have hcore0 := (data n).dualConnector_subset_narrow
      (slack n) gridVertex ⟨u, hu', rfl⟩
    have hcore : Pdual.shift
        ((data n).raw.data.baseDual + preferenceGridSite gridVertex) u ∈
        Edual.rectVertices 0 (extentX n) 0 (extentY n) := by
      simpa [(data n).raw.narrowRight_eq, (data n).raw.tallTop_eq]
        using hcore0
    rw [show (data n).raw.data.baseDual + preferenceGridSite gridVertex +
        horizontalShift (-(pad n)) =
      ((data n).raw.data.baseDual + preferenceGridSite gridVertex) +
        horizontalShift (-(pad n)) by abel, Pdual.shift_add]
    have hshift := (Edual.shift_mem_rectVertices
      (horizontalShift (-(pad n))) 0 (extentX n) 0 (extentY n) _).2 hcore
    have hshift' : Pdual.shift (horizontalShift (-(pad n)))
        (Pdual.shift
          ((data n).raw.data.baseDual + preferenceGridSite gridVertex) u) ∈
        Edual.rectVertices (0 - (pad n : Real))
          ((extentX n : Real) - pad n) 0 (extentY n) := by
      simpa [horizontalShift] using hshift
    apply Edual.rectVertices_mono le_rfl _ le_rfl le_rfl hshift'
    have hp : (0 : Real) <= pad n := by exact_mod_cast hpad n
    push_cast
    linarith
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n i
    have hTop : top n (i, 0) <= 1 := measureReal_le_one
    have hBottom : pDual n <= bottom n (i, 0) := by
      simpa [bottom, template, (data n).raw.shortTop_eq] using
        le_of_lt ((data n).raw.data.dual_bottom i)
    dsimp only [epsilon]
    linarith
  · intro n i
    have hBottom : bottom n (i, Fin.last ((data n).raw.data.heightDual)) <=
        1 := measureReal_le_one
    have hTop : pDual n <=
        top n (i, Fin.last ((data n).raw.data.heightDual)) := by
      simpa [top, template, (data n).raw.shortTop_eq] using
        le_of_lt ((data n).raw.data.dual_top i)
    dsimp only [epsilon]
    linarith
  · intro n j
    have hRight : right n (0, j) <= 1 := measureReal_le_one
    have hLeft : pDual n <= left n (0, j) := by
      simpa [left, template, (data n).raw.narrowRight_eq,
        (data n).raw.tallTop_eq] using
        le_of_lt ((data n).raw.data.dual_left j)
    dsimp only [epsilon]
    linarith
  · intro n j
    have hLeft : left n (Fin.last ((data n).raw.data.widthDual), j) <=
        1 := measureReal_le_one
    have hRight : pDual n <=
        right n (Fin.last ((data n).raw.data.widthDual), j) := by
      simpa [right, template, (data n).raw.narrowRight_eq,
        (data n).raw.tallTop_eq] using
        le_of_lt ((data n).raw.data.dual_right j)
    dsimp only [epsilon]
    linarith


theorem PeriodicPlaneEmbedding.alignedExact_primalMixedAdjacent_limit_of_pairMerge
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual
        (Pdual.orbitBox n) (pDual n))
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
    (schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n)
      (verticalRequirement n) (horizontalRequirement n))
    (k extentX extentY step radius : Nat -> Nat)
    (data : forall n, AlignedExactExtentPairedMixedBoundaryScores
      E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
      (p n) (pDual n) (family n) (familyDual n) (schedule n)
      (k n) (extentX n) (extentY n))
    (slack : forall n, PairedAlignedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n)
      (max (radius n) n) (k n))
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall n, p n <= 1)
    (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (P.orbitBox n)
        ((P.orbitBox n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        0 (extentX n) 0 (extentY n)))
      (mu.real (E.verticalCrossingEvent
        (data n).raw.data.wideLeft (data n).raw.data.wideRight
        0 (extentY n + step n)))) atTop (nhds 1) := by
  let template : Nat -> Finset V := fun n => P.orbitBox n
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  let epsilon : Nat -> Real := fun n => 1 - p n
  let bottom : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.width)
        ((data n).raw.data.height) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent
      (data n).raw.data.wideLeft (data n).raw.data.wideRight
      0 (extentY n)
      ((template n).image
        (P.shift ((data n).raw.data.base + preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices
        (data n).raw.data.wideLeft (data n).raw.data.wideRight
        0 (extentY n)))
  let top : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.width)
        ((data n).raw.data.height) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent
      (data n).raw.data.wideLeft (data n).raw.data.wideRight
      0 (extentY n)
      ((template n).image
        (P.shift ((data n).raw.data.base + preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices
        (data n).raw.data.wideLeft (data n).raw.data.wideRight
        0 (extentY n)))
  let left : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.width)
        ((data n).raw.data.height) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent 0 (extentX n) 0 (extentY n)
      ((template n).image
        (P.shift ((data n).raw.data.base + preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices 0 (extentX n) 0 (extentY n)))
  let right : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.width)
        ((data n).raw.data.height) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent 0 (extentX n) 0 (extentY n)
      ((template n).image
        (P.shift ((data n).raw.data.base + preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices 0 (extentX n) 0 (extentY n)))
  apply E.mixedAdjacentHeightPreference_crossing_max_tendsto_one_of_pairMerge
      mu hFKG hTI template htemplateHit (fun n => (step n : Int))
      (fun _ => Int.ofNat_zero_le _) radius
      (by simpa only [template] using hmerge)
      (fun n => (data n).raw.data.width)
      (fun n => (data n).raw.data.height)
      (fun n => (data n).raw.data.width_pos)
      (fun n => (data n).raw.data.height_pos)
      (fun n => (data n).raw.data.base)
      (fun _ => 0) (fun n => (extentX n : Real))
      (fun _ => 0) (fun n => (extentY n : Real))
      (fun n => (data n).raw.data.wideLeft)
      (fun n => (data n).raw.data.wideRight)
      (fun _ => 0) (fun n => (extentY n : Real))
      epsilon bottom top left right
  · simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hp
  · exact fun n => sub_nonneg.mpr (hp_le n)
  · exact fun n => (data n).raw.data.wideLeft_le
  · intro n
    simpa [(data n).raw.narrowRight_eq] using
      (data n).raw.data.narrowRight_le
  · exact fun _ => le_rfl
  · exact fun _ => le_rfl
  · intro n gridVertex vertex hvertex
    apply (data n).primalConnector_subset_narrow (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := by
      simpa only [template, Finset.mem_coe, Finset.mem_image] using hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    exact (Nat.le_max_right (radius n) n).trans
      (P.id_le_bufferedRadius (max (radius n) n))
  · intro n gridVertex vertex hvertex
    apply (data n).primalConnector_subset_narrow (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n gridVertex vertex hvertex
    rw [<- (data n).raw.shortTop_eq]
    apply (data n).primalConnector_subset_wide (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n i
    have hTop : top n (i, 0) <= 1 := measureReal_le_one
    have hBottom : p n <= bottom n (i, 0) := by
      simpa [bottom, template, (data n).raw.shortTop_eq] using
        le_of_lt ((data n).raw.data.primal_bottom i)
    dsimp only [epsilon]
    linarith
  · intro n i
    have hBottom : bottom n (i, Fin.last ((data n).raw.data.height)) <=
        1 := measureReal_le_one
    have hTop : p n <= top n (i, Fin.last ((data n).raw.data.height)) := by
      simpa [top, template, (data n).raw.shortTop_eq] using
        le_of_lt ((data n).raw.data.primal_top i)
    dsimp only [epsilon]
    linarith
  · intro n j
    have hRight : right n (0, j) <= 1 := measureReal_le_one
    have hLeft : p n <= left n (0, j) := by
      simpa [left, template, (data n).raw.narrowRight_eq,
        (data n).raw.tallTop_eq] using
        le_of_lt ((data n).raw.data.primal_left j)
    dsimp only [epsilon]
    linarith
  · intro n j
    have hLeft : left n (Fin.last ((data n).raw.data.width), j) <=
        1 := measureReal_le_one
    have hRight : p n <=
        right n (Fin.last ((data n).raw.data.width), j) := by
      simpa [right, template, (data n).raw.narrowRight_eq,
        (data n).raw.tallTop_eq] using
        le_of_lt ((data n).raw.data.primal_right j)
    dsimp only [epsilon]
    linarith


theorem PairedAdjacentBoundaryBandScheduleData.alignedExact_primalAdjacent_limit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {step : Nat -> Int}
    (scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (k extentX extentY : Nat -> Nat)
    (exact : forall n, AlignedExactExtentPairedMixedBoundaryScores
      E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
      (scheduleData.score n) (scheduleData.scoreDual n)
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n) (k n) (extentX n) (extentY n))
    (slack : forall n, PairedAlignedConnectorSlack E Edual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n)
      (max (scheduleData.radius n) n) (k n)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        0 (extentX n) 0 (extentY n)))
      (mu.real (E.verticalCrossingEvent
        (exact n).raw.data.wideLeft (exact n).raw.data.wideRight
        0 (extentY n + (step n).toNat)))) atTop (nhds 1) := by
  apply E.alignedExact_primalMixedAdjacent_limit_of_pairMerge
    Edual mu muDual hFKG hTI hunique
    scheduleData.score scheduleData.scoreDual
    scheduleData.family scheduleData.familyDual
    (fun n _ => max
      (E.connectorMarginRequirement (scheduleData.radius n))
      (Edual.connectorMarginRequirement (scheduleData.radiusDual n)))
    (fun n _ => max
      (E.connectorMarginRequirement (scheduleData.radius n))
      (Edual.connectorMarginRequirement (scheduleData.radiusDual n)))
    scheduleData.schedule
    k extentX extentY (fun n => (step n).toNat) scheduleData.radius
    exact slack scheduleData.score_tendsto scheduleData.score_le_one
  intro q
  apply (scheduleData.primalMerge q).congr'
  filter_upwards [] with n
  have hstep : ((step n).toNat : Int) = step n :=
    Int.toNat_of_nonneg (scheduleData.step_nonneg n)
  simp only [hstep]


theorem PairedAdjacentBoundaryBandScheduleData.exists_alignedExact_dualOutwardRadius
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {step : Nat -> Int}
    (scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    exists radius : Nat -> Nat,
      forall (k extentX extentY : Nat -> Nat)
        (exact : forall n, AlignedExactExtentPairedMixedBoundaryScores
          E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
          (scheduleData.score n) (scheduleData.scoreDual n)
          (scheduleData.family n) (scheduleData.familyDual n)
          (scheduleData.schedule n) (k n) (extentX n) (extentY n)),
        (forall n, PairedAlignedConnectorSlack E Edual
          (scheduleData.family n) (scheduleData.familyDual n)
          (scheduleData.schedule n) (max (radius n) n) (k n)) ->
        Tendsto (fun n => max
          (muDual.real (Edual.verticalCrossingEvent
            (exact n).raw.data.wideLeft (exact n).raw.data.wideRight
            (0 - (pad n : Real)) ((extentY n : Real) + pad n)))
          (muDual.real (Edual.horizontalCrossingEvent
            (0 - (pad n : Real)) ((extentX n : Real) + pad n)
            0 (extentY n)))) atTop (nhds 1) := by
  exact E.exists_uniformOrbitBoxOutwardMixedRadius_alignedExact_dualLimit
    Edual mu muDual hFKGDual hTIDual huniqueDual
    scheduleData.score scheduleData.scoreDual
    scheduleData.family scheduleData.familyDual
    (fun n _ => max
      (E.connectorMarginRequirement (scheduleData.radius n))
      (Edual.connectorMarginRequirement (scheduleData.radiusDual n)))
    (fun n _ => max
      (E.connectorMarginRequirement (scheduleData.radius n))
      (Edual.connectorMarginRequirement (scheduleData.radiusDual n)))
    scheduleData.schedule scheduleData.scoreDual_tendsto
    scheduleData.scoreDual_le_one pad hpad

omit [Countable V] in


theorem PeriodicPlaneEmbedding.orbitBoxCoordinateBound_mono_adaptive
    (E : PeriodicPlaneEmbedding P) {n m : Nat} (hnm : n <= m)
    (i : Fin 2) :
    E.orbitBoxCoordinateBound n i <= E.orbitBoxCoordinateBound m i := by
  classical
  unfold PeriodicPlaneEmbedding.orbitBoxCoordinateBound
  exact Finset.sup'_mono (fun v => |E.vertexCoord v i|)
    (fun _ hv => P.orbitBox_mono hnm hv)
    ⟨P.root, P.orbitBox_mono (Nat.zero_le n)
      P.root_mem_orbitBox_zero⟩

omit [Countable V] in


theorem PeriodicPlaneEmbedding.connectorMarginRequirement_mono_adaptive
    (E : PeriodicPlaneEmbedding P) {radius radius' : Nat}
    (h : radius <= radius') :
    E.connectorMarginRequirement radius <=
      E.connectorMarginRequirement radius' := by
  unfold PeriodicPlaneEmbedding.connectorMarginRequirement
  apply Nat.ceil_mono
  apply max_le_max
  · apply E.orbitBoxCoordinateBound_mono_adaptive
    exact P.bufferedRadius_strictMono.monotone h
  · apply E.orbitBoxCoordinateBound_mono_adaptive
    exact P.bufferedRadius_strictMono.monotone h

omit [Countable V] [Countable W] in


theorem PairedAlignedConnectorSlack.restrictRadius
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {radius radius' k : Nat} (h : radius <= radius')
    (slack : PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius' k) :
    PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius k := by
  have hprimal := E.connectorMarginRequirement_mono_adaptive h
  have hdual := Edual.connectorMarginRequirement_mono_adaptive h
  have hprimalInt : (E.connectorMarginRequirement radius : Int) <=
      E.connectorMarginRequirement radius' := by
    exact_mod_cast hprimal
  have hdualInt : (Edual.connectorMarginRequirement radius : Int) <=
      Edual.connectorMarginRequirement radius' := by
    exact_mod_cast hdual
  exact {
    primalLeft := hprimalInt.trans slack.primalLeft
    primalRight := by
      have := slack.primalRight
      omega
    primalBottom := hprimalInt.trans slack.primalBottom
    primalTop := by
      have := slack.primalTop
      omega
    dualLeft := hdualInt.trans slack.dualLeft
    dualRight := by
      have := slack.dualRight
      omega
    dualBottom := hdualInt.trans slack.dualBottom
    dualTop := by
      have := slack.dualTop
      omega }


end StatMech.FK.PeriodicPlanar
