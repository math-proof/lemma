/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part16
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_flipYConfig_involutive (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_flipYConfig (rlc_flipYConfig omega) = omega := by
  funext e
  rw [rlc_flipYConfig_apply, rlc_flipYConfig_apply]
  induction e using Sym2.inductionOn with
  | _ x y => simp

theorem rlc_flip_rightToUpper (n : ℤ)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (h : omega ∈ rlc_rightToUpper n) :
    rlc_flipYConfig omega ∈ rlc_rightToLower n := by
  have ht := rlc_flipY_lrRestricted_iff 0 (2 * n) n Set.univ rlc_upperHalf omega h
  simpa [rlc_rightToUpper, rlc_rightToLower, rlc_flipY_image_univ,
    rlc_flipY_image_upper] using ht

theorem rlc_flip_rightToLower (n : ℤ)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (h : omega ∈ rlc_rightToLower n) :
    rlc_flipYConfig omega ∈ rlc_rightToUpper n := by
  have ht := rlc_flipY_lrRestricted_iff 0 (2 * n) n Set.univ rlc_lowerHalf omega h
  simpa [rlc_rightToUpper, rlc_rightToLower, rlc_flipY_image_univ,
    rlc_flipY_image_lower] using ht

theorem rlc_flip_lowerToRight (n : ℤ)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (h : omega ∈ rlc_lowerToRight n) :
    rlc_flipYConfig omega ∈ rlc_upperToRight n := by
  have ht := rlc_flipY_lrRestricted_iff 0 (2 * n) n rlc_lowerHalf Set.univ omega h
  simpa [rlc_lowerToRight, rlc_upperToRight, rlc_flipY_image_univ,
    rlc_flipY_image_lower] using ht

theorem rlc_flip_upperToRight (n : ℤ)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (h : omega ∈ rlc_upperToRight n) :
    rlc_flipYConfig omega ∈ rlc_lowerToRight n := by
  have ht := rlc_flipY_lrRestricted_iff 0 (2 * n) n rlc_upperHalf Set.univ omega h
  simpa [rlc_lowerToRight, rlc_upperToRight, rlc_flipY_image_univ,
    rlc_flipY_image_upper] using ht

theorem rlc_rightToUpper_reflection_prob (p : ℝ≥0) (hp : p ≤ 1) (n : ℤ) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_rightToUpper n) =
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_rightToLower n) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hpre : rlc_flipYConfig ⁻¹' rlc_rightToUpper n = rlc_rightToLower n := by
    ext omega
    constructor
    · intro h
      have := rlc_flip_rightToUpper n h
      rwa [rlc_flipYConfig_involutive] at this
    · exact rlc_flip_rightToLower n
  calc
    mu.real (rlc_rightToUpper n) =
        mu.real (rlc_flipYConfig ⁻¹' rlc_rightToUpper n) :=
      ((rlc_flipY_measurePreserving p hp).measureReal_preimage
        (measurableSet_of_dependsOn
          (rlc_lrRestrictedEvent_dependsOn 0 (2 * n) (-n) n
            Set.univ rlc_upperHalf)).nullMeasurableSet).symm
    _ = mu.real (rlc_rightToLower n) := by rw [hpre]

theorem rlc_lowerToRight_reflection_prob (p : ℝ≥0) (hp : p ≤ 1) (n : ℤ) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_lowerToRight n) =
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_upperToRight n) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hpre : rlc_flipYConfig ⁻¹' rlc_lowerToRight n = rlc_upperToRight n := by
    ext omega
    constructor
    · intro h
      have := rlc_flip_lowerToRight n h
      rwa [rlc_flipYConfig_involutive] at this
    · exact rlc_flip_upperToRight n
  calc
    mu.real (rlc_lowerToRight n) =
        mu.real (rlc_flipYConfig ⁻¹' rlc_lowerToRight n) :=
      ((rlc_flipY_measurePreserving p hp).measureReal_preimage
        (measurableSet_of_dependsOn
          (rlc_lrRestrictedEvent_dependsOn 0 (2 * n) (-n) n
            rlc_lowerHalf Set.univ)).nullMeasurableSet).symm
    _ = mu.real (rlc_upperToRight n) := by rw [hpre]

theorem rlc_horizontal_subset_right_halves (n : ℤ) :
    horizontalCrossingEvent 0 (2 * n) (-n) n ⊆
      rlc_rightToUpper n ∪ rlc_rightToLower n := by
  rintro omega ⟨x, y, hxy⟩
  rcases le_total 0 ((y : Site 2) 1) with hy | hy
  · exact Or.inl ⟨x, y, Set.mem_univ _, hy, hxy⟩
  · exact Or.inr ⟨x, y, Set.mem_univ _, hy, hxy⟩

theorem rlc_horizontal_subset_left_halves (n : ℤ) :
    horizontalCrossingEvent 0 (2 * n) (-n) n ⊆
      rlc_lowerToRight n ∪ rlc_upperToRight n := by
  rintro omega ⟨x, y, hxy⟩
  rcases le_total 0 ((x : Site 2) 1) with hx | hx
  · exact Or.inr ⟨x, y, hx, Set.mem_univ _, hxy⟩
  · exact Or.inl ⟨x, y, hx, Set.mem_univ _, hxy⟩

theorem rlc_rightToUpper_half_localization (p : ℝ≥0) (hp : p ≤ 1)
    (n : ℤ) (alpha : ℝ)
    (hcross : alpha ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (horizontalCrossingEvent 0 (2 * n) (-n) n)) :
    alpha / 2 ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (rlc_rightToUpper n) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hmono : mu.real (horizontalCrossingEvent 0 (2 * n) (-n) n) ≤
      mu.real (rlc_rightToUpper n ∪ rlc_rightToLower n) :=
    measureReal_mono (rlc_horizontal_subset_right_halves n) (measure_ne_top _ _)
  have hunion := measureReal_union_le (μ := mu) (rlc_rightToUpper n) (rlc_rightToLower n)
  rw [← rlc_rightToUpper_reflection_prob p hp n] at hunion
  linarith

theorem rlc_lowerToRight_half_localization (p : ℝ≥0) (hp : p ≤ 1)
    (n : ℤ) (alpha : ℝ)
    (hcross : alpha ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (horizontalCrossingEvent 0 (2 * n) (-n) n)) :
    alpha / 2 ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (rlc_lowerToRight n) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hmono : mu.real (horizontalCrossingEvent 0 (2 * n) (-n) n) ≤
      mu.real (rlc_lowerToRight n ∪ rlc_upperToRight n) :=
    measureReal_mono (rlc_horizontal_subset_left_halves n) (measure_ne_top _ _)
  have hunion := measureReal_union_le (μ := mu) (rlc_lowerToRight n) (rlc_upperToRight n)
  rw [← rlc_lowerToRight_reflection_prob p hp n] at hunion
  linarith

theorem rlc_verticalCrossing_dependsOn (a b c d : ℤ) :
    DependsOn ((verticalCrossingEvent a b c d).indicator (fun _ => (1 : ℝ)))
      (edgesWithinFinset (rect_finite a b c d).toFinset : Set (Sym2 (Site 2))) := by
  let S := (rect_finite a b c d).toFinset
  have hSco : (S : Set (Site 2)) = rect a b c d := by
    ext z
    simp [S]
  intro omega omega' hagree
  have hconn : ∀ (x y : Site 2),
      (∃ (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d),
        ConnectedWithin 2 omega (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩) ↔
      (∃ (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d),
        ConnectedWithin 2 omega' (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩) := by
    intro x y
    rw [← hSco]
    exact withinConn_congr S x y hagree
  have hevent : omega ∈ verticalCrossingEvent a b c d ↔
      omega' ∈ verticalCrossingEvent a b c d := by
    constructor
    · rintro ⟨x, y, hxy⟩
      have hc : ∃ (hx : (x : Site 2) ∈ rect a b c d)
          (hy : (y : Site 2) ∈ rect a b c d),
          ConnectedWithin 2 omega (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩ :=
        ⟨bottomSide_subset x.2, topSide_subset y.2, hxy⟩
      obtain ⟨_, _, hc'⟩ := (hconn x y).mp hc
      exact ⟨x, y, hc'⟩
    · rintro ⟨x, y, hxy⟩
      have hc : ∃ (hx : (x : Site 2) ∈ rect a b c d)
          (hy : (y : Site 2) ∈ rect a b c d),
          ConnectedWithin 2 omega' (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩ :=
        ⟨bottomSide_subset x.2, topSide_subset y.2, hxy⟩
      obtain ⟨_, _, hc'⟩ := (hconn x y).mpr hc
      exact ⟨x, y, hc'⟩
  by_cases hmem : omega ∈ verticalCrossingEvent a b c d
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]


theorem rlc_rightDiagonal_lower_bound (p : ℝ≥0) (hp : p ≤ 1)
    (n : ℤ) (hn : 0 < n) (alpha : ℝ) (halpha : 0 ≤ alpha)
    (hH : alpha ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (horizontalCrossingEvent 0 (2 * n) (-n) n))
    (hV : alpha ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (verticalCrossingEvent 0 (2 * n) (-n) n)) :
    alpha ^ 3 / 4 ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (rlc_rightDiagonal n) := by
  let F := (rect_finite 0 (2 * n) (-n) n).toFinset
  apply rlc_diagonal_event_lower_bound p hp alpha halpha
    (rlc_rightToUpper n) (rlc_lowerToRight n)
    (verticalCrossingEvent 0 (2 * n) (-n) n) (rlc_rightDiagonal n)
    (edgesWithinFinset F) (edgesWithinFinset F) (edgesWithinFinset F)
  · exact rlc_lrRestrictedEvent_isIncreasing _ _ _ _ _ _
  · exact rlc_lrRestrictedEvent_isIncreasing _ _ _ _ _ _
  · exact StatMech.RSW.Strip.verticalCrossingEvent_isIncreasing _ _ _ _
  · simpa [F, rlc_rightToUpper] using
      rlc_lrRestrictedEvent_dependsOn 0 (2 * n) (-n) n Set.univ rlc_upperHalf
  · simpa [F, rlc_lowerToRight] using
      rlc_lrRestrictedEvent_dependsOn 0 (2 * n) (-n) n rlc_lowerHalf Set.univ
  · simpa [F] using rlc_verticalCrossing_dependsOn 0 (2 * n) (-n) n
  · exact rlc_rightToUpper_half_localization p hp n alpha hH
  · exact rlc_lowerToRight_half_localization p hp n alpha hH
  · exact hV
  · exact rlc_rightDiagonal_of_three n hn


end Universality
end StatMech
