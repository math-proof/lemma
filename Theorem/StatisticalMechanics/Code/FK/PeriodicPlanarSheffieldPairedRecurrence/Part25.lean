/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part17
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem PairedAdjacentBoundaryBandTransition.local_limits
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {step : Nat -> Int}
    (data : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (transition : PairedAdjacentBoundaryBandTransition data) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)))
      (mu.real (E.verticalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n))))
      atTop (nhds 1) /\
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n))))
      atTop (nhds 1) /\
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n))))
      atTop (nhds 1) := by
  refine ⟨?_, transition.lower.dual_limit data,
    transition.upper.dual_limit data⟩
  simpa only [transition.upper_a, transition.upper_b,
    transition.upper_c, transition.upper_d] using
      transition.lower.primalAdjacent_limit data


theorem PairedAdjacentBoundaryBandTransition.false_of_endpoints_and_matched
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual] {step : Nat -> Int}
    (data : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (transition : PairedAdjacentBoundaryBandTransition data)
    (hverticalStart : Tendsto (fun n => mu.real
      (E.verticalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)))
      atTop (nhds 1))
    (hhorizontalEnd : Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)))
      atTop (nhds 1))
    (hmatchHorizontalLower : forall n,
      mu.real (E.horizontalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)) +
      muDual.real (Edual.verticalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)) <= 1)
    (hmatchVerticalLower : forall n,
      mu.real (E.verticalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)) +
      muDual.real (Edual.horizontalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)) <= 1)
    (hmatchHorizontalUpper : forall n,
      mu.real (E.horizontalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)) +
      muDual.real (Edual.verticalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)) <= 1)
    (hmatchVerticalUpper : forall n,
      mu.real (E.verticalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)) +
      muDual.real (Edual.horizontalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)) <= 1) : False := by
  let horizontal : Nat -> Nat -> Real := fun n k =>
    if k = 0 then mu.real (E.horizontalCrossingEvent
      (transition.lower.a n) (transition.lower.b n)
      (transition.lower.c n) (transition.lower.d n))
    else mu.real (E.horizontalCrossingEvent
      (transition.upper.a n) (transition.upper.b n)
      (transition.upper.c n) (transition.upper.d n))
  let vertical : Nat -> Nat -> Real := fun n k =>
    if k = 0 then mu.real (E.verticalCrossingEvent
      (transition.lower.a n) (transition.lower.b n)
      (transition.lower.c n) (transition.lower.d n))
    else mu.real (E.verticalCrossingEvent
      (transition.upper.a n) (transition.upper.b n)
      (transition.upper.c n) (transition.upper.d n))
  let dualVertical : Nat -> Nat -> Real := fun n k =>
    if k = 0 then muDual.real (Edual.verticalCrossingEvent
      (transition.lower.a n) (transition.lower.b n)
      (transition.lower.c n) (transition.lower.d n))
    else muDual.real (Edual.verticalCrossingEvent
      (transition.upper.a n) (transition.upper.b n)
      (transition.upper.c n) (transition.upper.d n))
  let dualHorizontal : Nat -> Nat -> Real := fun n k =>
    if k = 0 then muDual.real (Edual.horizontalCrossingEvent
      (transition.lower.a n) (transition.lower.b n)
      (transition.lower.c n) (transition.lower.d n))
    else muDual.real (Edual.horizontalCrossingEvent
      (transition.upper.a n) (transition.upper.b n)
      (transition.upper.c n) (transition.upper.d n))
  obtain ⟨hprimal, hdualLower, hdualUpper⟩ :=
    transition.local_limits data
  apply adjacent_height_array_contradiction_of_primal_dual_limits
    horizontal vertical dualVertical dualHorizontal (fun _ => 0)
    (fun n k => by
      by_cases hk : k = 0 <;> simp [horizontal, hk, measureReal_nonneg])
    (fun n k => by
      by_cases hk : k = 0 <;> simp [vertical, hk, measureReal_nonneg])
    (fun n k => by
      by_cases hk : k = 0 <;> simp [horizontal, hk, measureReal_le_one])
    (fun n k => by
      by_cases hk : k = 0 <;> simp [vertical, hk, measureReal_le_one])
  · simpa only [vertical, if_pos] using hverticalStart
  · simpa only [horizontal, Nat.zero_add, if_false, one_ne_zero] using
      hhorizontalEnd
  · intro n k
    by_cases hk : k = 0
    · simpa [horizontal, dualVertical, hk] using hmatchHorizontalLower n
    · simpa [horizontal, dualVertical, hk] using hmatchHorizontalUpper n
  · intro n k
    by_cases hk : k = 0
    · simpa [vertical, dualHorizontal, hk] using hmatchVerticalLower n
    · simpa [vertical, dualHorizontal, hk] using hmatchVerticalUpper n
  · intro k hk
    have hk0 : forall n, k n = 0 := by
      intro n
      have := hk n
      omega
    simpa only [horizontal, vertical, hk0, if_pos, Nat.zero_add,
      if_false, one_ne_zero] using hprimal
  · intro k
    let lower : Nat -> Real := fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (transition.lower.a n) (transition.lower.b n)
        (transition.lower.c n) (transition.lower.d n)))
    let upper : Nat -> Real := fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (transition.upper.a n) (transition.upper.b n)
        (transition.upper.c n) (transition.upper.d n)))
    have hlower : Tendsto lower atTop (nhds 1) := by
      simpa only [lower] using hdualLower
    have hupper : Tendsto upper atTop (nhds 1) := by
      simpa only [upper] using hdualUpper
    have hmin : Tendsto (fun n => min (lower n) (upper n))
        atTop (nhds 1) := by
      simpa only [min_self] using hlower.min hupper
    apply hmin.squeeze tendsto_const_nhds
    · intro n
      by_cases hk : k n = 0
      · simpa only [dualVertical, dualHorizontal, hk, if_pos, lower] using
          (min_le_left (lower n) (upper n))
      · simpa only [dualVertical, dualHorizontal, hk, if_neg, upper] using
          (min_le_right (lower n) (upper n))
    · intro n
      by_cases hk : k n = 0
      · simp only [dualVertical, dualHorizontal, hk, if_pos]
        exact max_le measureReal_le_one measureReal_le_one
      · simp only [dualVertical, dualHorizontal, hk, if_neg]
        exact max_le measureReal_le_one measureReal_le_one


end StatMech.FK.PeriodicPlanar
