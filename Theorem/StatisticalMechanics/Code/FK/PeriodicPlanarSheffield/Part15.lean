/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part15
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem measurable_sqrt_trick
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {A B : Set (ConfigSpace (Sym2 V))}
    (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    1 - Real.sqrt (1 - mu.real (A ∪ B)) <=
      max (mu.real A) (mu.real B) := by
  have hfkg := hFKG A B hAm hBm hA hB
  have hie : mu.real (A ∪ B) + mu.real (A ∩ B) =
      mu.real A + mu.real B := measureReal_union_add_inter hBm
  apply Universality.sqrt_trick_max_real measureReal_le_one measureReal_le_one
  nlinarith


theorem four_event_sqrt_trick
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {A B C D : Set (ConfigSpace (Sym2 V))}
    (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hC : IsIncreasing C) (hD : IsIncreasing D)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hCm : MeasurableSet C) (hDm : MeasurableSet D) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤
      max (max (mu.real A) (mu.real B))
        (max (mu.real C) (mu.real D)) := by
  have houter := measurable_sqrt_trick mu hFKG
    (hA.union hB) (hC.union hD) (hAm.union hBm) (hCm.union hDm)
  simp only [Set.union_assoc] at houter
  have hAB := measurable_sqrt_trick mu hFKG hA hB hAm hBm
  have hCD := measurable_sqrt_trick mu hFKG hC hD hCm hDm
  by_cases hle : mu.real (A ∪ B) ≤ mu.real (C ∪ D)
  · rw [max_eq_right hle] at houter
    have hmiss : 1 - mu.real (C ∪ D) ≤
        Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D)))) := by
      linarith
    have hsqrt := Real.sqrt_le_sqrt hmiss
    exact le_trans (by linarith)
      (le_max_right (max (mu.real A) (mu.real B))
        (max (mu.real C) (mu.real D)))
  · have hle' : mu.real (C ∪ D) ≤ mu.real (A ∪ B) := le_of_not_ge hle
    rw [max_eq_left hle'] at houter
    have hmiss : 1 - mu.real (A ∪ B) ≤
        Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D)))) := by
      linarith
    have hsqrt := Real.sqrt_le_sqrt hmiss
    exact le_trans (by linarith)
      (le_max_left (max (mu.real A) (mu.real B))
        (max (mu.real C) (mu.real D)))

theorem four_event_max_tendsto_one
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (A B C D : ℕ → Set (ConfigSpace (Sym2 V)))
    (hA : ∀ n, IsIncreasing (A n)) (hB : ∀ n, IsIncreasing (B n))
    (hC : ∀ n, IsIncreasing (C n)) (hD : ∀ n, IsIncreasing (D n))
    (hAm : ∀ n, MeasurableSet (A n)) (hBm : ∀ n, MeasurableSet (B n))
    (hCm : ∀ n, MeasurableSet (C n)) (hDm : ∀ n, MeasurableSet (D n))
    (hunion : Tendsto (fun n =>
      mu.real (A n ∪ (B n ∪ (C n ∪ D n)))) atTop (nhds 1)) :
    Tendsto (fun n => max (max (mu.real (A n)) (mu.real (B n)))
      (max (mu.real (C n)) (mu.real (D n)))) atTop (nhds 1) := by
  have hmiss : Tendsto (fun n =>
      1 - mu.real (A n ∪ (B n ∪ (C n ∪ D n)))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hunion
  have hlower : Tendsto (fun n => 1 - Real.sqrt (Real.sqrt
      (1 - mu.real (A n ∪ (B n ∪ (C n ∪ D n))))))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · intro n
    exact four_event_sqrt_trick mu hFKG
      (hA n) (hB n) (hC n) (hD n)
      (hAm n) (hBm n) (hCm n) (hDm n)
  · intro n
    exact max_le (max_le measureReal_le_one measureReal_le_one)
      (max_le measureReal_le_one measureReal_le_one)


theorem min_tendsto_zero_of_matched_exclusion
    (primalH primalV dualV dualH : ℕ → ℝ)
    (hH0 : ∀ n, 0 ≤ primalH n) (hV0 : ∀ n, 0 ≤ primalV n)
    (hmatchH : ∀ n, primalH n + dualV n ≤ 1)
    (hmatchV : ∀ n, primalV n + dualH n ≤ 1)
    (hdual : Tendsto (fun n => max (dualV n) (dualH n)) atTop (nhds 1)) :
    Tendsto (fun n => min (primalH n) (primalV n)) atTop (nhds 0) := by
  have hupper : ∀ n,
      min (primalH n) (primalV n) ≤
        1 - max (dualV n) (dualH n) := by
    intro n
    by_cases hle : dualV n ≤ dualH n
    · rw [max_eq_right hle]
      exact (min_le_right _ _).trans (by linarith [hmatchV n])
    · rw [max_eq_left (le_of_not_ge hle)]
      exact (min_le_left _ _).trans (by linarith [hmatchH n])
  have hrhs : Tendsto (fun n => 1 - max (dualV n) (dualH n))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hdual
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0 : ℝ))) hrhs
  · intro n
    exact le_min (hH0 n) (hV0 n)
  · exact hupper


theorem balanced_aspect_crossing_contradiction
    (h v hNext vNext : ℕ → ℝ)
    (hbalance : ∀ n, h n ≤ v n)
    (hnext : ∀ n, vNext n < hNext n)
    (hmax : Tendsto (fun n => max (h n) (vNext n)) atTop (nhds 1))
    (hmin : Tendsto (fun n => min (v n) (h n)) atTop (nhds 0))
    (hminNext : Tendsto (fun n => min (vNext n) (hNext n))
      atTop (nhds 0)) : False := by
  have hh : Tendsto h atTop (nhds 0) := by
    convert hmin using 1
    funext n
    exact (min_eq_right (hbalance n)).symm
  have hvNext : Tendsto vNext atTop (nhds 0) := by
    convert hminNext using 1
    funext n
    exact (min_eq_left (hnext n).le).symm
  have hmaxZero : Tendsto (fun n => max (h n) (vNext n))
      atTop (nhds 0) := by
    simpa using hh.max hvNext
  have h01 : (1 : ℝ) = 0 := tendsto_nhds_unique hmax hmaxZero
  norm_num at h01


theorem balanced_aspect_crossing_contradiction_of_error
    (h v hNext vNext error : ℕ → ℝ)
    (hh0 : ∀ n, 0 ≤ h n) (hvNext0 : ∀ n, 0 ≤ vNext n)
    (herror0 : ∀ n, 0 ≤ error n)
    (hbalance : ∀ n, h n ≤ v n + error n)
    (hnext : ∀ n, vNext n ≤ hNext n + error n)
    (herror : Tendsto error atTop (nhds 0))
    (hmax : Tendsto (fun n => max (h n) (vNext n)) atTop (nhds 1))
    (hmin : Tendsto (fun n => min (v n) (h n)) atTop (nhds 0))
    (hminNext : Tendsto (fun n => min (vNext n) (hNext n))
      atTop (nhds 0)) : False := by
  have hhUpper : ∀ n, h n ≤ min (v n) (h n) + error n := by
    intro n
    by_cases hvh : v n ≤ h n
    · rw [min_eq_left hvh]
      exact hbalance n
    · rw [min_eq_right (le_of_not_ge hvh)]
      exact le_add_of_nonneg_right (herror0 n)
  have hvNextUpper : ∀ n,
      vNext n ≤ min (vNext n) (hNext n) + error n := by
    intro n
    by_cases hvh : vNext n ≤ hNext n
    · rw [min_eq_left hvh]
      exact le_add_of_nonneg_right (herror0 n)
    · rw [min_eq_right (le_of_not_ge hvh)]
      exact hnext n
  have hh : Tendsto h atTop (nhds 0) := by
    have hupper : Tendsto (fun n => min (v n) (h n) + error n)
        atTop (nhds 0) := by
      simpa only [zero_add] using hmin.add herror
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds (x := (0 : ℝ))) hupper
    · exact hh0
    · exact hhUpper
  have hvNext : Tendsto vNext atTop (nhds 0) := by
    have hupper : Tendsto (fun n => min (vNext n) (hNext n) + error n)
        atTop (nhds 0) := by
      simpa only [zero_add] using hminNext.add herror
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds (x := (0 : ℝ))) hupper
    · exact hvNext0
    · exact hvNextUpper
  have hmaxZero : Tendsto (fun n => max (h n) (vNext n))
      atTop (nhds 0) := by
    simpa using hh.max hvNext
  have h01 : (1 : ℝ) = 0 := tendsto_nhds_unique hmax hmaxZero
  norm_num at h01


end StatMech.FK.PeriodicPlanar
