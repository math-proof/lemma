/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part11
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem nonempty_radiusFirstAdjacentEndpointRow
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
    (B r y s : Real) (hB0 : 0 <= B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (t : Int) (ht : 3 * B < t)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Int)
    (hhorizontalSpan : forall radius w,
      minimumWidth radius <= w ->
      3 * B < horizontalRight w - horizontalLeft w) :
    Nonempty (RadiusFirstAdjacentEndpointRow E Edual mu muDual template
      step cutoff epsilon B r y s t minimumWidth minimumHeight
      horizontalLeft horizontalRight) := by
  obtain ⟨radius, width, height, hradius, hwidth, hheight,
      hmerge, hvertical, hhorizontal⟩ :=
    exists_radiusFirst_adjacentEndpointRow E Edual mu muDual hunique
      hFKGDual hTIDual huniqueDual template step cutoff epsilon hepsilon
      B r y s hB0 hB t ht minimumWidth minimumHeight
      horizontalLeft horizontalRight hhorizontalSpan
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


theorem exists_recursiveRadiusFirstAdjacentEndpointRows_with_limits
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
    (r y s : Nat -> Int -> Real) (t : Nat -> Int -> Int)
    (ht : forall n step, 3 * B < t n step)
    (minimumWidth minimumHeight : Nat -> Int -> Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Int -> Nat -> Int)
    (hhorizontalSpan : forall n step radius width,
      minimumWidth n step radius <= width ->
      3 * B < horizontalRight n step width -
        horizontalLeft n step width) :
    let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
    exists state : Nat -> Int × Nat,
      exists rows : forall n, RadiusFirstAdjacentEndpointRow E Edual mu
        muDual (template n) (state n).1 (state n).2 (epsilon n) B
        (r n (state n).1) (y n (state n).1) (s n (state n).1)
        (t n (state n).1) (minimumWidth n (state n).1)
        (minimumHeight n (state n).1) (horizontalLeft n (state n).1)
        (horizontalRight n (state n).1),
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
        (r n (state n).1) (r n (state n).1 + (rows n).width)
        ((2 * s n (state n).1 +
          (s n (state n).1 + t n (state n).1)) / 3)
        ((s n (state n).1 +
          2 * (s n (state n).1 + t n (state n).1)) / 3)))
        atTop (nhds 1) /\
      Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
        (horizontalLeft n (state n).1 (rows n).width)
        (horizontalRight n (state n).1 (rows n).width)
        (y n (state n).1) (y n (state n).1 + (rows n).height)))
        atTop (nhds 1) := by
  dsimp only
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  let chooseRow (n : Nat) (state : Int × Nat) := Classical.choice
    (nonempty_radiusFirstAdjacentEndpointRow E Edual mu muDual hunique
      hFKGDual hTIDual huniqueDual (template n) state.1 state.2
      (epsilon n) (hepsilon n) B (r n state.1) (y n state.1)
      (s n state.1) hB0 hB (t n state.1) (ht n state.1)
      (minimumWidth n state.1) (minimumHeight n state.1)
      (horizontalLeft n state.1) (horizontalRight n state.1)
      (hhorizontalSpan n state.1))
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
        (r n (state n).1) (r n (state n).1 + (rows n).width)
        ((2 * s n (state n).1 +
          (s n (state n).1 + t n (state n).1)) / 3)
        ((s n (state n).1 +
          2 * (s n (state n).1 + t n (state n).1)) / 3)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (rows n).dualVertical_gt)
      (fun _ => measureReal_le_one)
  have hhorizontal : Tendsto (fun n => muDual.real
      (Edual.horizontalCrossingEvent
        (horizontalLeft n (state n).1 (rows n).width)
        (horizontalRight n (state n).1 (rows n).width)
        (y n (state n).1) (y n (state n).1 + (rows n).height)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (rows n).dualHorizontal_gt)
      (fun _ => measureReal_le_one)
  exact ⟨state, rows, hstate0, hstateSucc, hstepNonneg, hradiusTop,
    hmerge, hmergeShift, hvertical, hhorizontal⟩


end StatMech.FK.PeriodicPlanar
