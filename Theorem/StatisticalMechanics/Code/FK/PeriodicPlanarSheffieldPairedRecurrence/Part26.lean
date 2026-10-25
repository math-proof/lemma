/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part18
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem PeriodicPlanarDualPair.PaddedPairedAdjacentTransition.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {step pad : Nat -> Int}
    (data : PairedAdjacentOutwardScheduleData D.primalEmbedding
      D.dualEmbedding mu (D.dualMeasure mu) step pad)
    (transition : D.PaddedPairedAdjacentTransition mu data)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (hpad : forall n, 4 * B <= (pad n : Real))
    (hspanX0 : forall n, transition.a0 n + 5 * B <
      transition.b0 n - 5 * B)
    (hspanY0 : forall n, transition.c0 n + 5 * B <
      transition.d0 n - 5 * B)
    (hspanX1 : forall n, transition.a1 n + 5 * B <
      transition.b1 n - 5 * B)
    (hspanY1 : forall n, transition.c1 n + 5 * B <
      transition.d1 n - 5 * B) : False := by
  let padReal : Nat -> Real := fun n => pad n
  have hprimal := (transition.primal.local_limits data.base).1
  have hprimal' : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (transition.a0 n) (transition.b0 n)
        (transition.c0 n + padReal n) (transition.d0 n - padReal n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (transition.a1 n + padReal n) (transition.b1 n - padReal n)
        (transition.c1 n) (transition.d1 n)))) atTop (nhds 1) := by
    simpa only [padReal, transition.primalLower_a,
      transition.primalLower_b, transition.primalLower_c,
      transition.primalLower_d, transition.primalUpper_a,
      transition.primalUpper_b, transition.primalUpper_c,
      transition.primalUpper_d] using hprimal
  have hdualLower := transition.dualLower.crossing_limit data
  have hdualLower' : Tendsto (fun n => max
      ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        (transition.a0 n + padReal n) (transition.b0 n - padReal n)
        (transition.c0 n) (transition.d0 n)))
      ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        (transition.a0 n) (transition.b0 n)
        (transition.c0 n + padReal n) (transition.d0 n - padReal n))))
      atTop (nhds 1) := by
    simpa only [padReal, transition.dualLower_a,
      transition.dualLower_b, transition.dualLower_c,
      transition.dualLower_d, add_sub_cancel_right, sub_add_cancel]
      using hdualLower
  have hdualUpper := transition.dualUpper.crossing_limit data
  have hdualUpper' : Tendsto (fun n => max
      ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        (transition.a1 n + padReal n) (transition.b1 n - padReal n)
        (transition.c1 n) (transition.d1 n)))
      ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        (transition.a1 n) (transition.b1 n)
        (transition.c1 n + padReal n) (transition.d1 n - padReal n))))
      atTop (nhds 1) := by
    simpa only [padReal, transition.dualUpper_a,
      transition.dualUpper_b, transition.dualUpper_c,
      transition.dualUpper_d, add_sub_cancel_right, sub_add_cancel]
      using hdualUpper
  obtain ⟨hdual0, hdual1⟩ := D.dualMeasure_twoLevel_outward_limits mu
    transition.a0 transition.b0 transition.c0 transition.d0
    transition.a1 transition.b1 transition.c1 transition.d1
    padReal padReal padReal padReal hdualLower' hdualUpper'
  apply D.variablePadTwoLevel_false_of_normal_rotated_limits mu B hBpos
    hBp hBd transition.a0 transition.b0 transition.c0 transition.d0
    transition.a1 transition.b1 transition.c1 transition.d1
    padReal padReal padReal padReal hpad hpad hpad hpad
    hspanX0 hspanY0 hspanX1 hspanY1
  · simpa only [padReal] using transition.verticalStart
  · simpa only [padReal] using transition.horizontalEnd
  · exact hprimal'
  · exact hdual0
  · exact hdual1


theorem PeriodicPlaneEmbedding.deepPreferenceGrid_orbitBox_subset_rect
    (E : PeriodicPlaneEmbedding P) (R M width height margin : Nat)
    (hx : E.orbitBoxCoordinateBound R (0 : Fin 2) <= M + margin)
    (hy : E.orbitBoxCoordinateBound R (1 : Fin 2) <= M + margin)
    (v : PreferenceGridVertex width height)
    (hvLeft : margin <= v.1.val)
    (hvRight : v.1.val + margin < width)
    (hvBottom : margin <= v.2.val)
    (hvTop : v.2.val + margin < height) :
    P.shift (preferenceGridSite v) '' (P.orbitBox R : Set V) <=
      E.rectVertices (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real) := by
  rintro _ ⟨u, hu, rfl⟩
  have hu0 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hu (0 : Fin 2)
  have hu1 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hu (1 : Fin 2)
  rw [abs_le] at hu0 hu1
  have hxR : E.orbitBoxCoordinateBound R (0 : Fin 2) <=
      (M + margin : Real) := by exact_mod_cast hx
  have hyR : E.orbitBoxCoordinateBound R (1 : Fin 2) <=
      (M + margin : Real) := by exact_mod_cast hy
  have hleftR : (margin : Real) <= v.1.val := by exact_mod_cast hvLeft
  have hrightR : (v.1.val : Real) + margin < width := by
    exact_mod_cast hvRight
  have hbottomR : (margin : Real) <= v.2.val := by
    exact_mod_cast hvBottom
  have htopR : (v.2.val : Real) + margin < height := by
    exact_mod_cast hvTop
  change (-(M : Real) <=
      E.vertexCoord (P.shift (preferenceGridSite v) u) 0 /\
    E.vertexCoord (P.shift (preferenceGridSite v) u) 0 <= M + width /\
    -(M : Real) <= E.vertexCoord (P.shift (preferenceGridSite v) u) 1 /\
    E.vertexCoord (P.shift (preferenceGridSite v) u) 1 <= M + height)
  simp only [E.vertexCoord_shift]
  simp only [preferenceGridSite, Pi.add_apply, Int.cast_natCast]
  constructor
  · linarith [hu0.1]
  constructor
  · linarith [hu0.2]
  constructor
  · linarith [hu1.1]
  · linarith [hu1.2]


theorem PeriodicPlaneEmbedding.exists_coupled_endpointCrossings_tendsto_one_of_unique
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r y B s : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (t : Int) (ht : 3 * B < t)
    (minimumWidth minimumHeight : Nat -> Nat)
    (hminimumWidth : forall n,
      3 * B < 3 * (minimumWidth n : Real)) :
    exists width height : Nat -> Nat,
      (forall n, minimumWidth n <= width n) /\
      (forall n, minimumHeight n <= height n) /\
      Tendsto (fun n => mu.real (E.verticalCrossingEvent
        r (r + width n)
        ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)))
        atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.horizontalCrossingEvent
        r (r + width n) y (y + height n))) atTop (nhds 1) := by
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  choose width hwidth hvertical using fun n =>
    E.exists_verticalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique r B s hB0 hB t ht (minimumWidth n)
        (hepsilon n)
  have hwidthB (n : Nat) : 3 * B < 3 * (width n : Real) := by
    exact (hminimumWidth n).trans_le (by
      gcongr
      exact_mod_cast hwidth n)
  let horizontalS : Nat -> Real := fun n => r - width n
  let horizontalT : Nat -> Int := fun n => 3 * (width n : Int)
  have hhorizontalT (n : Nat) : 3 * B < horizontalT n := by
    dsimp only [horizontalT]
    exact_mod_cast hwidthB n
  choose height hheight hhorizontal using fun n =>
    E.exists_horizontalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique y B (horizontalS n) hB0 hB
        (horizontalT n) (hhorizontalT n) (minimumHeight n) (hepsilon n)
  have hlower : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
      simpa only [epsilon] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  have hverticalLimit : Tendsto (fun n => mu.real
      (E.verticalCrossingEvent r (r + width n)
        ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (hvertical n)) (fun _ => measureReal_le_one)
  have hhorizontalLimit : Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent r (r + width n) y (y + height n)))
      atTop (nhds 1) := by
    have hlowerHorizontal : forall n, 1 - epsilon n < mu.real
        (E.horizontalCrossingEvent r (r + width n) y (y + height n)) := by
      intro n
      convert hhorizontal n using 1 <;>
        simp only [horizontalS, horizontalT, Int.cast_mul,
          Int.cast_ofNat, Int.cast_natCast] <;> ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds (fun n => le_of_lt (hlowerHorizontal n))
        (fun _ => measureReal_le_one)
  exact ⟨width, height, hwidth, hheight,
    hverticalLimit, hhorizontalLimit⟩


theorem PeriodicPlaneEmbedding.exists_dependentSpan_endpointCrossings_tendsto_one_of_unique
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r y B s : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (t : Int) (ht : 3 * B < t)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Nat -> Int)
    (hhorizontalSpan : forall n w, minimumWidth n <= w ->
      3 * B < horizontalRight n w - horizontalLeft n w) :
    exists width height : Nat -> Nat,
      (forall n, minimumWidth n <= width n) /\
      (forall n, minimumHeight n <= height n) /\
      Tendsto (fun n => mu.real (E.verticalCrossingEvent
        r (r + width n)
        ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)))
        atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.horizontalCrossingEvent
        (horizontalLeft n (width n)) (horizontalRight n (width n))
        y (y + height n))) atTop (nhds 1) := by
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  choose width hwidth hvertical using fun n =>
    E.exists_verticalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique r B s hB0 hB t ht (minimumWidth n)
        (hepsilon n)
  let horizontalS : Nat -> Real := fun n =>
    2 * horizontalLeft n (width n) - horizontalRight n (width n)
  let horizontalT : Nat -> Int := fun n =>
    3 * (horizontalRight n (width n) - horizontalLeft n (width n))
  have hhorizontalT (n : Nat) : 3 * B < horizontalT n := by
    have hspan := hhorizontalSpan n (width n) (hwidth n)
    rw [show (horizontalT n : Real) =
        3 * ((horizontalRight n (width n) : Real) -
          horizontalLeft n (width n)) by
      simp only [horizontalT, Int.cast_mul, Int.cast_ofNat, Int.cast_sub]]
    nlinarith
  choose height hheight hhorizontal using fun n =>
    E.exists_horizontalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique y B (horizontalS n) hB0 hB
        (horizontalT n) (hhorizontalT n) (minimumHeight n) (hepsilon n)
  have hlower : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
      simpa only [epsilon] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  have hverticalLimit : Tendsto (fun n => mu.real
      (E.verticalCrossingEvent r (r + width n)
        ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (hvertical n)) (fun _ => measureReal_le_one)
  have hhorizontalLimit : Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent
        (horizontalLeft n (width n)) (horizontalRight n (width n))
        y (y + height n))) atTop (nhds 1) := by
    have hlowerHorizontal : forall n, 1 - epsilon n < mu.real
        (E.horizontalCrossingEvent
          (horizontalLeft n (width n)) (horizontalRight n (width n))
          y (y + height n)) := by
      intro n
      convert hhorizontal n using 1 <;>
        simp only [horizontalS, horizontalT, Int.cast_mul,
          Int.cast_ofNat, Int.cast_sub] <;> ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds (fun n => le_of_lt (hlowerHorizontal n))
        (fun _ => measureReal_le_one)
  exact ⟨width, height, hwidth, hheight,
    hverticalLimit, hhorizontalLimit⟩


theorem PeriodicPlaneEmbedding.exists_rowwise_dependentSpan_endpointCrossings_tendsto_one_of_unique
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (r y s : Nat -> Real) (t : Nat -> Int)
    (ht : forall n, 3 * B < t n)
    (epsilon : Nat -> Real) (hepsilon : forall n, 0 < epsilon n)
    (hepsilon_zero : Tendsto epsilon atTop (nhds 0))
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Nat -> Int)
    (hhorizontalSpan : forall n w, minimumWidth n <= w ->
      3 * B < horizontalRight n w - horizontalLeft n w) :
    exists width height : Nat -> Nat,
      (forall n, minimumWidth n <= width n) /\
      (forall n, minimumHeight n <= height n) /\
      Tendsto (fun n => mu.real (E.verticalCrossingEvent
        (r n) (r n + width n)
        ((2 * s n + (s n + t n)) / 3)
        ((s n + 2 * (s n + t n)) / 3))) atTop (nhds 1) /\
      Tendsto (fun n => mu.real (E.horizontalCrossingEvent
        (horizontalLeft n (width n)) (horizontalRight n (width n))
        (y n) (y n + height n))) atTop (nhds 1) := by
  choose width hwidth hvertical using fun n =>
    E.exists_verticalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique (r n) B (s n) hB0 hB (t n) (ht n)
        (minimumWidth n) (hepsilon n)
  let horizontalS : Nat -> Real := fun n =>
    2 * horizontalLeft n (width n) - horizontalRight n (width n)
  let horizontalT : Nat -> Int := fun n =>
    3 * (horizontalRight n (width n) - horizontalLeft n (width n))
  have hhorizontalT (n : Nat) : 3 * B < horizontalT n := by
    have hspan := hhorizontalSpan n (width n) (hwidth n)
    rw [show (horizontalT n : Real) =
        3 * ((horizontalRight n (width n) : Real) -
          horizontalLeft n (width n)) by
      simp only [horizontalT, Int.cast_mul, Int.cast_ofNat, Int.cast_sub]]
    nlinarith
  choose height hheight hhorizontal using fun n =>
    E.exists_horizontalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique (y n) B (horizontalS n) hB0 hB
        (horizontalT n) (hhorizontalT n) (minimumHeight n) (hepsilon n)
  have hlower : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilon_zero
  have hverticalLimit : Tendsto (fun n => mu.real
      (E.verticalCrossingEvent (r n) (r n + width n)
        ((2 * s n + (s n + t n)) / 3)
        ((s n + 2 * (s n + t n)) / 3))) atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
      (fun n => le_of_lt (hvertical n)) (fun _ => measureReal_le_one)
  have hhorizontalLimit : Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent
        (horizontalLeft n (width n)) (horizontalRight n (width n))
        (y n) (y n + height n))) atTop (nhds 1) := by
    have hlowerHorizontal : forall n, 1 - epsilon n < mu.real
        (E.horizontalCrossingEvent
          (horizontalLeft n (width n)) (horizontalRight n (width n))
          (y n) (y n + height n)) := by
      intro n
      convert hhorizontal n using 1 <;>
        simp only [horizontalS, horizontalT, Int.cast_mul,
          Int.cast_ofNat, Int.cast_sub] <;> ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds (fun n => le_of_lt (hlowerHorizontal n))
        (fun _ => measureReal_le_one)
  exact ⟨width, height, hwidth, hheight,
    hverticalLimit, hhorizontalLimit⟩


end StatMech.FK.PeriodicPlanar
