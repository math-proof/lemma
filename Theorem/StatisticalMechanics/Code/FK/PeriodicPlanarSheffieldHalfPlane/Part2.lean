/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlane.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicGraph.setConnectionWithin_measurableSet
    (P : PeriodicGraph V) (A S T : Set V) :
    MeasurableSet (P.setConnectionWithin A S T) := by
  have heq : P.setConnectionWithin A S T =
      ⋃ x : V, ⋃ (_hx : x ∈ S), ⋃ y : V, ⋃ (_hy : y ∈ T),
        P.connectedWithinSet A x y := by
    ext omega
    simp [PeriodicGraph.setConnectionWithin]
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
      P.connectedWithinSet_measurableSet A x y

theorem PeriodicGraph.setConnectionWithin_isIncreasing
    (P : PeriodicGraph V) (A S T : Set V) :
    IsIncreasing (P.setConnectionWithin A S T) := by
  intro omega eta home
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    P.connectedWithinSet_isIncreasing A x y home hxy⟩

theorem PeriodicGraph.setConnectionWithin_union_target
    (P : PeriodicGraph V) (A S T U : Set V) :
    P.setConnectionWithin A S (T ∪ U) =
      P.setConnectionWithin A S T ∪ P.setConnectionWithin A S U := by
  ext omega
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    rcases hy with hy | hy
    · exact Or.inl ⟨x, hx, y, hy, hxy⟩
    · exact Or.inr ⟨x, hx, y, hy, hxy⟩
  · rintro (h | h)
    · obtain ⟨x, hx, y, hy, hxy⟩ := h
      exact ⟨x, hx, y, Or.inl hy, hxy⟩
    · obtain ⟨x, hx, y, hy, hxy⟩ := h
      exact ⟨x, hx, y, Or.inr hy, hxy⟩


theorem directional_sqrt_trick
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {A B : Set (ConfigSpace (Sym2 V))}
    (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hBA : mu.real B ≤ mu.real A) :
    1 - Real.sqrt (1 - mu.real (A ∪ B)) ≤ mu.real A := by
  have h := measurable_sqrt_trick mu hFKG hA hB hAm hBm
  rwa [max_eq_left hBA] at h


theorem three_event_intersection_lower_bound
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {A B C : Set (ConfigSpace (Sym2 V))}
    (hBm : MeasurableSet B) (hCm : MeasurableSet C) :
    mu.real A + mu.real B + mu.real C - 2 ≤
      mu.real ((A ∩ B) ∩ C) := by
  have pairLower {S T : Set (ConfigSpace (Sym2 V))}
      (hTm : MeasurableSet T) :
      mu.real S + mu.real T - 1 ≤ mu.real (S ∩ T) := by
    have hie := measureReal_union_add_inter (μ := mu) (s := S) hTm
    have hu : mu.real (S ∪ T) ≤ 1 := measureReal_le_one
    linarith
  have hAB := pairLower (S := A) (T := B) hBm
  have hABC := pairLower (S := A ∩ B) (T := C) hCm
  linarith


end StatMech.FK.PeriodicPlanar
