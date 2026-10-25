/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part19
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem nonempty_dependentRadiusFirstAdjacentEndpointRow
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (template : Finset V) (step : Int) (cutoff : Nat)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (r y s : Nat -> Real) (t : Nat -> Int)
    (ht : forall radius, 3 * B < t radius)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Nat -> Int)
    (hhorizontalSpan : forall radius width,
      minimumWidth radius <= width ->
      3 * B < horizontalRight radius width -
        horizontalLeft radius width) :
    Nonempty (DependentRadiusFirstAdjacentEndpointRow E Edual mu muDual
      template step cutoff epsilon B r y s t minimumWidth minimumHeight
      horizontalLeft horizontalRight) := by
  obtain ⟨radius, width, height, hradius, hwidth, hheight,
      hmerge, hvertical, hhorizontal⟩ :=
    exists_radiusFirst_dependentGeometry_adjacentEndpointRow
      E Edual mu muDual hunique hFKGDual hTIDual huniqueDual template
      step cutoff epsilon hepsilon B hB0 hB r y s t ht minimumWidth
      minimumHeight horizontalLeft horizontalRight hhorizontalSpan
  exact ⟨{
    radius := radius
    width := width
    height := height
    cutoff_le_radius := hradius
    minimumWidth_le := hwidth
    minimumHeight_le := hheight
    merge_lt := hmerge
    dualVertical_gt := hvertical
    dualHorizontal_gt := hhorizontal }⟩


theorem exists_recursiveDependentRadiusFirstAdjacentEndpointRows_with_limits
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (template : Nat -> Finset V) (initialStep : Int)
    (hinitialStep : 0 <= initialStep)
    (r y s : Nat -> Int -> Nat -> Real)
    (t : Nat -> Int -> Nat -> Int)
    (ht : forall n step radius, 3 * B < t n step radius)
    (minimumWidth minimumHeight : Nat -> Int -> Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Int -> Nat -> Nat -> Int)
    (hhorizontalSpan : forall n step radius width,
      minimumWidth n step radius <= width ->
      3 * B < horizontalRight n step radius width -
        horizontalLeft n step radius width) :
    let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
    exists state : Nat -> Int × Nat,
      exists rows : forall n, DependentRadiusFirstAdjacentEndpointRow
        E Edual mu muDual (template n) (state n).1 (state n).2
        (epsilon n) B (r n (state n).1) (y n (state n).1)
        (s n (state n).1) (t n (state n).1)
        (minimumWidth n (state n).1) (minimumHeight n (state n).1)
        (horizontalLeft n (state n).1) (horizontalRight n (state n).1),
      state 0 = (initialStep, 0) /\
      (forall n, state (n + 1) =
        (((rows n).height : Int), (rows n).radius + 1)) /\
      (forall n, 0 <= (state n).1) /\
      Tendsto (fun n => (rows n).radius) atTop atTop /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
          ((template n).image (P.shift
            (preferenceKingOffset (q n).2 +
              if (q n).1.val = 0 then 0
              else verticalShift (state n).1))) (rows n).radius))
          atTop (nhds 0)) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (state (n + 1)).1)))
            (rows (n + 1)).radius)) atTop (nhds 0)) /\
      Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
        (r n (state n).1 (rows n).radius)
        (r n (state n).1 (rows n).radius + (rows n).width)
        ((2 * s n (state n).1 (rows n).radius +
          (s n (state n).1 (rows n).radius +
            t n (state n).1 (rows n).radius)) / 3)
        ((s n (state n).1 (rows n).radius +
          2 * (s n (state n).1 (rows n).radius +
            t n (state n).1 (rows n).radius)) / 3)))
        atTop (nhds 1) /\
      Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
        (horizontalLeft n (state n).1 (rows n).radius (rows n).width)
        (horizontalRight n (state n).1 (rows n).radius (rows n).width)
        (y n (state n).1 (rows n).radius)
        (y n (state n).1 (rows n).radius + (rows n).height)))
        atTop (nhds 1) := by
  dsimp only
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  let chooseRow (n : Nat) (state : Int × Nat) := Classical.choice
    (nonempty_dependentRadiusFirstAdjacentEndpointRow
      E Edual mu muDual hunique hFKGDual hTIDual huniqueDual
      (template n) state.1 state.2 (epsilon n) (hepsilon n) B hB0 hB
      (r n state.1) (y n state.1) (s n state.1) (t n state.1)
      (ht n state.1) (minimumWidth n state.1)
      (minimumHeight n state.1) (horizontalLeft n state.1)
      (horizontalRight n state.1) (hhorizontalSpan n state.1))
  let state : Nat -> Int × Nat := fun n =>
    Nat.rec (initialStep, 0) (fun n previous =>
      let row := chooseRow n previous
      ((row.height : Int), row.radius + 1)) n
  let rows := fun n => chooseRow n (state n)
  have hstate0 : state 0 = (initialStep, 0) := rfl
  have hstateSucc (n : Nat) : state (n + 1) =
      (((rows n).height : Int), (rows n).radius + 1) := by
    simp only [state, rows]
  have hstepNonneg : forall n, 0 <= (state n).1 := by
    intro n
    cases n with
    | zero => simpa only [hstate0] using hinitialStep
    | succ n =>
        rw [hstateSucc n]
        exact Int.ofNat_zero_le _
  have hcutoffCofinal : forall n, n <= (state n).2 := by
    intro n
    induction n with
    | zero => simp only [hstate0, le_refl]
    | succ n ih =>
        rw [hstateSucc n]
        exact Nat.succ_le_succ (ih.trans (rows n).cutoff_le_radius)
  have hradiusCofinal : forall n, n <= (rows n).radius := fun n =>
    (hcutoffCofinal n).trans (rows n).cutoff_le_radius
  have hradiusTop : Tendsto (fun n => (rows n).radius) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hradiusCofinal n)
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    simpa only [epsilon] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hmerge (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0
            else verticalShift (state n).1))) (rows n).radius))
        atTop (nhds 0) := by
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => le_of_lt ((rows n).merge_lt (q n))) hepsilonZero
  have hmergeShift (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real
        (P.pairMergeErrorUnion (template (n + 1))
          ((template (n + 1)).image (P.shift
            (preferenceKingOffset (q (n + 1)).2 +
              if (q (n + 1)).1.val = 0 then 0
              else verticalShift (state (n + 1)).1)))
          (rows (n + 1)).radius)) atTop (nhds 0) := by
    exact (hmerge q).comp (tendsto_add_atTop_nat 1)
  have hlower : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  have hvertical : Tendsto (fun n => muDual.real
      (Edual.verticalCrossingEvent
        (r n (state n).1 (rows n).radius)
        (r n (state n).1 (rows n).radius + (rows n).width)
        ((2 * s n (state n).1 (rows n).radius +
          (s n (state n).1 (rows n).radius +
            t n (state n).1 (rows n).radius)) / 3)
        ((s n (state n).1 (rows n).radius +
          2 * (s n (state n).1 (rows n).radius +
            t n (state n).1 (rows n).radius)) / 3)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (rows n).dualVertical_gt)
      (fun _ => measureReal_le_one)
  have hhorizontal : Tendsto (fun n => muDual.real
      (Edual.horizontalCrossingEvent
        (horizontalLeft n (state n).1 (rows n).radius (rows n).width)
        (horizontalRight n (state n).1 (rows n).radius (rows n).width)
        (y n (state n).1 (rows n).radius)
        (y n (state n).1 (rows n).radius + (rows n).height)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (rows n).dualHorizontal_gt)
      (fun _ => measureReal_le_one)
  exact ⟨state, rows, hstate0, hstateSucc, hstepNonneg, hradiusTop,
    hmerge, hmergeShift, hvertical, hhorizontal⟩


theorem exists_carriedAsymmetricEndpointCoordinates_with_limits
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Nat) (hBpos : 0 < B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (template : Nat -> Finset V) :
    let targetY : Nat -> Nat := fun n => 20 * B + n + 1
    exists radius width height : Nat -> Nat,
      Tendsto radius atTop atTop /\
      (forall n, 3 * B + 1 <= width n) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (height n))))
            (radius (n + 1)))) atTop (nhds 0)) /\
      Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
        (4 * B) (4 * B + width n) (-4 * B)
          (targetY n + 4 * B))) atTop (nhds 1) /\
      Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
        (-4 * B) (width n + 12 * B) (4 * B)
          (4 * B + height n))) atTop (nhds 1) /\
      (forall n, (0 : Real) + 5 * B < width n + 8 * B - 5 * B) /\
      (forall n, -(4 * B : Real) + 5 * B <
        targetY n + 4 * B - 5 * B) /\
      (forall n, -(4 * B : Real) + 5 * B <
        width n + 12 * B - 5 * B) /\
      (forall n, (0 : Real) + 5 * B <
        targetY n + height n - 5 * B) /\
      (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\
      (forall n, (4 * B : Real) + width n <=
        width n + 8 * B - 4 * B) /\
      (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\
      (forall n, (4 * B : Real) + height n <=
        targetY n + height n - 4 * B) := by
  dsimp only
  let targetY : Nat -> Nat := fun n => 20 * B + n + 1
  let r : Nat -> Int -> Nat -> Real := fun _ _ _ => 4 * B
  let y : Nat -> Int -> Nat -> Real := fun _ _ _ => 4 * B
  let s : Nat -> Int -> Nat -> Real := fun n _ _ =>
    -(targetY n : Real) - 12 * B
  let t : Nat -> Int -> Nat -> Int := fun n _ _ =>
    (3 * targetY n + 24 * B : Nat)
  let minimumWidth : Nat -> Int -> Nat -> Nat := fun _ _ _ => 3 * B + 1
  let minimumHeight : Nat -> Int -> Nat -> Nat := fun _ _ _ => 0
  let horizontalLeft : Nat -> Int -> Nat -> Nat -> Int := fun _ _ _ _ =>
    -(4 * (B : Int))
  let horizontalRight : Nat -> Int -> Nat -> Nat -> Int := fun _ _ _ w =>
    w + 12 * (B : Int)
  have ht (n : Nat) (step : Int) (radius : Nat) :
      3 * (B : Real) < t n step radius := by
    dsimp only [t, targetY]
    push_cast
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hn : (0 : Real) <= n := by positivity
    nlinarith
  have hhorizontalSpan (n : Nat) (step : Int) (radius width : Nat)
      (_hwidth : minimumWidth n step radius <= width) :
      3 * (B : Real) <
        horizontalRight n step radius width -
          horizontalLeft n step radius width := by
    dsimp only [horizontalRight, horizontalLeft]
    push_cast
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hw : (0 : Real) <= width := by positivity
    nlinarith
  obtain ⟨state, rows, _hstate0, hstateSucc, _hstepNonneg,
      hradius, _hmerge, hmergeShift, hvertical, hhorizontal⟩ :=
    exists_recursiveDependentRadiusFirstAdjacentEndpointRows_with_limits
      E Edual mu muDual hunique hFKGDual hTIDual huniqueDual
      (B : Real) (by positivity) hB template 0 (by omega)
      r y s t ht minimumWidth minimumHeight horizontalLeft horizontalRight
        hhorizontalSpan
  let radius : Nat -> Nat := fun n => (rows n).radius
  let width : Nat -> Nat := fun n => (rows n).width
  let height : Nat -> Nat := fun n => (rows n).height
  have hstateStep (n : Nat) : (state (n + 1)).1 = (height n : Int) := by
    rw [hstateSucc n]
  have hmergeCarried
      (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real
        (P.pairMergeErrorUnion (template (n + 1))
          ((template (n + 1)).image (P.shift
            (preferenceKingOffset (q (n + 1)).2 +
              if (q (n + 1)).1.val = 0 then 0
              else verticalShift (height n))))
          (radius (n + 1)))) atTop (nhds 0) := by
    apply (hmergeShift q).congr'
    filter_upwards [] with n
    simp only [hstateStep n, radius]
  have hvertical' : Tendsto (fun n => muDual.real
      (Edual.verticalCrossingEvent (4 * B) (4 * B + width n)
        (-4 * B) (targetY n + 4 * B))) atTop (nhds 1) := by
    apply hvertical.congr'
    filter_upwards [] with n
    congr 2 <;> dsimp only [r, s, t, targetY, width] <;> push_cast <;> ring
  have hhorizontal' : Tendsto (fun n => muDual.real
      (Edual.horizontalCrossingEvent (-4 * B) (width n + 12 * B)
        (4 * B) (4 * B + height n))) atTop (nhds 1) := by
    apply hhorizontal.congr'
    filter_upwards [] with n
    congr 2 <;>
      dsimp only [horizontalLeft, horizontalRight, y, width, height] <;>
      push_cast <;> ring
  have hwidthLower (n : Nat) : 3 * B + 1 <= width n :=
    (rows n).minimumWidth_le
  refine ⟨radius, width, height, hradius, hwidthLower, hmergeCarried,
    hvertical', hhorizontal', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hw : (3 * B + 1 : Real) <= width n := by exact_mod_cast hwidthLower n
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    norm_num at hw ⊢
    linarith
  · intro n
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hn : (0 : Real) <= n := by positivity
    push_cast
    nlinarith
  · intro n
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hw : (0 : Real) <= width n := by positivity
    push_cast
    linarith
  · intro n
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hy : (10 * B : Real) < targetY n := by
      dsimp only [targetY]
      push_cast
      have hn : (0 : Real) <= n := by positivity
      nlinarith
    have hh : (0 : Real) <= height n := by positivity
    push_cast
    linarith
  · intro n
    norm_num
  · intro n
    have hBreal : (0 : Real) <= B := by positivity
    push_cast
    linarith
  · intro n
    norm_num
  · intro n
    have hy : (8 * B : Real) <= targetY n := by
      dsimp only [targetY]
      push_cast
      have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
      have hn : (0 : Real) <= n := by positivity
      nlinarith
    push_cast
    linarith


theorem PeriodicPlanarDualPair.exists_carriedAsymmetricEndpoints_false_of_primal_limit
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (huniqueDual : (D.dualMeasure mu)
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Nat) (hBpos : 0 < B)
    (hBp : forall {x z : V} (hxz : P.graph.Adj x z)
      (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxz u -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxz u -
          D.dualEmbedding.vertex x) i| <= B)
    (template : Nat -> Finset V) :
    let targetY : Nat -> Nat := fun n => 20 * B + n + 1
    exists radius width height : Nat -> Nat,
      Tendsto radius atTop atTop /\
      (forall n, 3 * B + 1 <= width n) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (height n))))
            (radius (n + 1)))) atTop (nhds 0)) /\
      (Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          0 (width n + 8 * B) 0 (targetY n)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          0 (width n + 8 * B) 0 (targetY n + height n))))
        atTop (nhds 1) -> False) := by
  dsimp only
  let targetY : Nat -> Nat := fun n => 20 * B + n + 1
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  obtain ⟨radius, width, height, hradius, hwidth, hmerge,
      hdualV0, hdualH0, hspanHX, hspanDVY, hspanDHX, hspanVY,
      hDVLeft, hDVRight, hDHBottom, hDHTop⟩ :=
    exists_carriedAsymmetricEndpointCoordinates_with_limits
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      hunique hFKGDual hTIDual huniqueDual B hBpos hBd template
  have hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (4 * B) (4 * B + width n) (-4 * B)
          (targetY n + 4 * B))) atTop (nhds 1) := by
    apply hdualV0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
  have hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (-4 * B) (width n + 12 * B) (4 * B)
          (4 * B + height n))) atTop (nhds 1) := by
    apply hdualH0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
  have hspanDVY' : forall n,
      -(4 * B : Real) + 5 * B <
        (targetY n : Real) + 4 * B - 5 * B := by
    simpa only [targetY] using hspanDVY
  have hspanVY' : forall n,
      (0 : Real) + 5 * B <
        (targetY n : Real) + height n - 5 * B := by
    simpa only [targetY] using hspanVY
  have hDHTop' : forall n,
      (4 * B : Real) + height n <=
        (targetY n : Real) + height n - 4 * B := by
    simpa only [targetY] using hDHTop
  refine ⟨radius, width, height, hradius, hwidth, hmerge, ?_⟩
  intro hprimal
  exact D.fullyAsymmetricEndpointCoordinates_false mu (B : Real)
    (by exact_mod_cast hBpos) hBp hBd
    (fun _ => 0) (fun n => width n + 8 * B)
    (fun _ => 0) (fun n => (targetY n : Real))
    (fun _ => 0) (fun n => width n + 8 * B)
    (fun _ => 0) (fun n => (targetY n : Real) + height n)
    (fun _ => 4 * B) (fun n => 4 * B + width n)
    (fun _ => -4 * B) (fun n => targetY n + 4 * B)
    (fun _ => -4 * B) (fun n => width n + 12 * B)
    (fun _ => 4 * B) (fun n => 4 * B + height n)
    hspanHX (fun n => by nlinarith [hspanDVY' n])
    (fun n => by nlinarith [hspanDHX n]) hspanVY'
    (fun _ => by norm_num) (fun _ => by norm_num)
    hDVLeft hDVRight
    (fun _ => by norm_num) (fun _ => by apply le_of_eq; ring)
    hDHBottom hDHTop'
    hprimal hdualV hdualH


theorem PeriodicPlaneEmbedding.exists_uniformOrbitBoxMixedRadius_alignedExact_primalLimit
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
    (schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall n, p n <= 1) :
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
          (mu.real (E.horizontalCrossingEvent
            0 (extentX n) 0 (extentY n)))
          (mu.real (E.verticalCrossingEvent
            (data n).raw.data.wideLeft (data n).raw.data.wideRight
            0 (extentY n)))) atTop (nhds 1) := by
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
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  refine ⟨radius, ?_⟩
  intro k extentX extentY data slack
  apply hcross
      (fun n => (data n).raw.data.width)
      (fun n => (data n).raw.data.height)
      (fun n => (data n).raw.data.width_pos)
      (fun n => (data n).raw.data.height_pos)
      (fun n => (data n).raw.data.base)
      (fun _ => 0) (fun n => (extentX n : Real))
      (fun _ => 0) (fun n => (extentY n : Real))
      (fun n => (data n).raw.data.wideLeft)
      (fun n => (data n).raw.data.wideRight)
      (fun _ => 0) (fun n => (extentY n : Real)) p hp hp_le
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
  · intro n i
    simpa [template, (data n).raw.shortTop_eq] using
      le_of_lt ((data n).raw.data.primal_bottom i)
  · intro n i
    simpa [template, (data n).raw.shortTop_eq] using
      le_of_lt ((data n).raw.data.primal_top i)
  · intro n j
    simpa [template, (data n).raw.narrowRight_eq,
      (data n).raw.tallTop_eq] using
      le_of_lt ((data n).raw.data.primal_left j)
  · intro n j
    simpa [template, (data n).raw.narrowRight_eq,
      (data n).raw.tallTop_eq] using
      le_of_lt ((data n).raw.data.primal_right j)

set_option maxHeartbeats 800000 in


theorem PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.primalAdjacent_limit_of_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (S : Nat -> Finset V) (margin M width height radius : Nat -> Nat)
    (score : Nat -> Real)
    (data : forall n, E.CommonSquareNormalBoundaryBandData
      mu (S n) (margin n) (M n) (score n))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (hwidth : forall n, 2 * margin n < width n)
    (hheight : forall n, 2 * margin n < height n)
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
      (v : PreferenceGridVertex (width n) (height n)),
      margin n <= v.1.val -> v.1.val + margin n < width n ->
      margin n <= v.2.val -> v.2.val + margin n < height n ->
      (P.shift (preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (-(M n : Real)) (M n + width n)
            (-(M n : Real)) (M n + height n)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (-(M n : Real)) (M n + width n)
        (-(M n : Real)) (M n + height n)))
      (mu.real (E.verticalCrossingEvent
        (-(M n : Real)) (M n + width n)
        (-(M n : Real)) (M n + height n + step n))))
      atTop (nhds 1) := by
  let template : Nat -> Finset V := fun n =>
    P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight
      (data n).zBottom (data n).zTop
  have hcontinuation :
      E.UniformTemplateAdjacentBoundaryBandCrossingRadius
        mu template step radius :=
    E.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_pairMerge
      mu hFKG hTI template (by simpa only [template] using htemplateHit)
        step hstep radius (by simpa only [template] using hmerge)
  apply hcontinuation width height margin (fun _ => 0)
    (fun n => -(M n : Real)) (fun n => M n + width n)
    (fun n => -(M n : Real)) (fun n => M n + height n) score
    hwidth hheight hscore_le hscore
  · intro n v
    have hsource := E.fourShiftTemplate_preferenceGrid_subset_rect
      (M n) (width n) (height n) (S n)
      (data n).zLeft (data n).zRight (data n).zBottom (data n).zTop
      (by simpa [Finset.coe_image, horizontalShift] using
        ((data n).left (0 : Fin (margin n + 1))).1)
      (by simpa [Finset.coe_image, horizontalShift] using
        ((data n).right (0 : Fin (margin n + 1))).1)
      (by simpa [Finset.coe_image, verticalShift] using
        ((data n).bottom (0 : Fin (margin n + 1))).1)
      (by simpa [Finset.coe_image, verticalShift] using
        ((data n).top (0 : Fin (margin n + 1))).1) v
    simpa only [template, Pi.zero_apply, zero_add] using hsource
  · simpa only [Pi.zero_apply, zero_add] using hconnector
  · intro n v hv
    simpa only [template, Pi.zero_apply, zero_add] using
      le_of_lt ((data n).bottomBandScore E mu hTI (width n) (height n) v hv)
  · intro n v hv
    simpa only [template, Pi.zero_apply, zero_add] using
      le_of_lt ((data n).topBandScore E mu hTI (width n) (height n) v hv)
  · intro n v hv
    simpa only [template, Pi.zero_apply, zero_add] using
      le_of_lt ((data n).leftBandScore E mu hTI (width n) (height n) v hv)
  · intro n v hv
    simpa only [template, Pi.zero_apply, zero_add] using
      le_of_lt ((data n).rightBandScore E mu hTI (width n) (height n) v hv)


theorem PeriodicPlaneEmbedding.nonempty_carriedCrossNestedArray_of_alignedSharedLevelSteps
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (S : Nat -> Finset V) (score : Nat -> Real)
    (family : forall m, E.NormalBoundaryBandFamily mu (S m) (score m))
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
    (state : Nat -> Nat × Nat) (K : Nat -> Nat)
    (scoreEpsilon mergeEpsilon : Nat -> Real)
    (steps : forall n, E.AlignedSharedLevelStep mu S score family
      verticalRequirement horizontalRequirement
      (state n).1 (state n).2 (scoreEpsilon n) (mergeEpsilon n))
    (hscoreEpsilon : Tendsto scoreEpsilon atTop (nhds 0))
    (hmergeEpsilon : Tendsto mergeEpsilon atTop (nhds 0))
    (hextentK : forall n, (steps n).extent <= K n)
    (hverticalConnector : forall n,
      (P.orbitBox (P.bufferedRadius (steps n).nextConnector) : Set V) <=
        E.rectVertices (-(K n : Real)) (K n)
          (-(steps n).extent : Real) (steps n).extent)
    (hhorizontalConnector : forall n,
      (P.orbitBox (P.bufferedRadius (steps n).nextConnector) : Set V) <=
        E.rectVertices (-(steps n).extent : Real) (steps n).extent
          (-(K n : Real)) (K n)) :
    Nonempty (E.CarriedCrossNestedArray mu) := by
  have hlower : Tendsto (fun n => 1 - scoreEpsilon n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hscoreEpsilon
  have hbottom : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).bottom : Set V)
        (E.rectBottomBoundaryVertices
          (-(steps n).extent : Real) (steps n).extent
          (-(steps n).extent : Real) (steps n).extent)))
      atTop (nhds 1) :=
    hlower.squeeze tendsto_const_nhds
      (fun n => le_of_lt ((steps n).threshold_gt.trans
        (steps n).bottomComponentScore))
      (fun _ => measureReal_le_one)
  have htop : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).top : Set V)
        (E.rectTopBoundaryVertices
          (-(steps n).extent : Real) (steps n).extent
          (-(steps n).extent : Real) (steps n).extent)))
      atTop (nhds 1) :=
    hlower.squeeze tendsto_const_nhds
      (fun n => le_of_lt ((steps n).threshold_gt.trans
        (steps n).topComponentScore))
      (fun _ => measureReal_le_one)
  have hleft : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).left : Set V)
        (E.rectLeftBoundaryVertices
          (-(steps n).extent : Real) (steps n).extent
          (-(steps n).extent : Real) (steps n).extent)))
      atTop (nhds 1) :=
    hlower.squeeze tendsto_const_nhds
      (fun n => le_of_lt ((steps n).threshold_gt.trans
        (steps n).leftComponentScore))
      (fun _ => measureReal_le_one)
  have hright : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent
        (-(steps n).extent : Real) (steps n).extent
        (-(steps n).extent : Real) (steps n).extent
        ((steps n).right : Set V)
        (E.rectRightBoundaryVertices
          (-(steps n).extent : Real) (steps n).extent
          (-(steps n).extent : Real) (steps n).extent)))
      atTop (nhds 1) :=
    hlower.squeeze tendsto_const_nhds
      (fun n => le_of_lt ((steps n).threshold_gt.trans
        (steps n).rightComponentScore))
      (fun _ => measureReal_le_one)
  have hverticalMerge : Tendsto (fun n => mu.real
      (P.pairMergeErrorUnion (steps n).bottom (steps n).top
        (steps n).nextConnector)) atTop (nhds 0) :=
    squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => le_of_lt (steps n).verticalMerge) hmergeEpsilon
  have hhorizontalMerge : Tendsto (fun n => mu.real
      (P.pairMergeErrorUnion (steps n).left (steps n).right
        (steps n).nextConnector)) atTop (nhds 0) :=
    squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => le_of_lt (steps n).horizontalMerge) hmergeEpsilon
  exact ⟨{
    a := fun n => -(steps n).extent
    b := fun n => (steps n).extent
    c := fun n => -(steps n).extent
    d := fun n => (steps n).extent
    aWide := fun n => -(K n : Real)
    bWide := fun n => K n
    cTall := fun n => -(K n : Real)
    dTall := fun n => K n
    bottom := fun n => (steps n).bottom
    top := fun n => (steps n).top
    left := fun n => (steps n).left
    right := fun n => (steps n).right
    verticalRadius := fun n => (steps n).nextConnector
    horizontalRadius := fun n => (steps n).nextConnector
    wideLeft := fun n => by
      exact neg_le_neg (by exact_mod_cast (hextentK n))
    wideRight := fun n => by exact_mod_cast (hextentK n)
    tallBottom := fun n => by
      exact neg_le_neg (by exact_mod_cast (hextentK n))
    tallTop := fun n => by exact_mod_cast (hextentK n)
    verticalConnector := hverticalConnector
    horizontalConnector := hhorizontalConnector
    bottomLimit := hbottom
    topLimit := htop
    leftLimit := hleft
    rightLimit := hright
    verticalMergeLimit := hverticalMerge
    horizontalMergeLimit := hhorizontalMerge }⟩

end StatMech.FK.PeriodicPlanar
