/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleSqrtTrick
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry.Part5
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


@[simp] theorem bdcLongRectangleOriginIndex_event (alpha n : ℕ)
    (ha : 0 < alpha) :
    bdcLongRectangleEvent alpha n (bdcLongRectangleOriginIndex alpha ha) =
      bdcLongRectangleBaseEvent alpha n := by
  ext omega
  simp [bdcLongRectangleEvent, bdcLongRectangleBaseEvent,
    bdcLongRectangleOriginIndex, bdcLongRectangleXOffset,
    bdcLongRectangleYOffset]


@[simp] theorem bdcLongRectangleOriginIndex_mem (alpha : ℕ)
    (ha : 0 < alpha) :
    bdcLongRectangleOriginIndex alpha ha ∈ bdcLongRectangleIndices alpha := by
  simp [bdcLongRectangleIndices]


theorem bdcLongRectangle_polynomial_deficit
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure mu]
    (hpa : PositivelyAssociated mu)
    (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu)
    {alpha n : ℕ} (ha : 0 < alpha) (hn : 1 ≤ n)
    {c epsilon : ℝ} (hc : 0 ≤ c)
    (hunion : 1 - mu.real (bdcLongRectangleUnion alpha n) ≤
      c * (n : ℝ) ^ (-epsilon)) :
    1 - c ^ ((1 : ℝ) / (2 * alpha ^ 3 : ℕ)) *
        (n : ℝ) ^ (-epsilon / (2 * alpha ^ 3 : ℕ)) ≤
      mu.real (bdcLongRectangleBaseEvent alpha n) := by
  let i0 := bdcLongRectangleOriginIndex alpha ha
  have h := finite_symmetric_polynomial_deficit mu hpa
    (bdcLongRectangleIndices alpha) (bdcLongRectangleEvent alpha n)
    (i₀ := i0) (bdcLongRectangleOriginIndex_mem alpha ha)
    (fun k _ => bdcLongRectangleEvent_isIncreasing alpha n k)
    (fun k _ => bdcLongRectangleEvent_measurableSet alpha n k)
    (fun k _ => by
      rw [bdcLongRectangleOriginIndex_event]
      exact bdcLongRectangleEvent_probability_eq mu hshift alpha n k)
    hc hn hunion
  simpa [i0, bdcLongRectangleIndices_card,
    bdcLongRectangleOriginIndex_event] using h


theorem bdcLongRectangleUnion_deficit_of_cover
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))) [IsFiniteMeasure mu]
    {alpha n : ℕ} (B : Set (ConfigSpace (Sym2 (Site 2))))
    (hcover : B ⊆ bdcLongRectangleUnion alpha n)
    {c epsilon : ℝ}
    (hB : 1 - mu.real B ≤ c * (n : ℝ) ^ (-epsilon)) :
    1 - mu.real (bdcLongRectangleUnion alpha n) ≤
      c * (n : ℝ) ^ (-epsilon) := by
  have hmono : mu.real B ≤
      mu.real (bdcLongRectangleUnion alpha n) :=
    measureReal_mono hcover
  linarith


theorem bdcLongRectangle_polynomial_deficit_of_cover
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure mu]
    (hpa : PositivelyAssociated mu)
    (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu)
    {alpha n : ℕ} (ha : 0 < alpha) (hn : 1 ≤ n)
    (B : Set (ConfigSpace (Sym2 (Site 2))))
    (hcover : B ⊆ bdcLongRectangleUnion alpha n)
    {c epsilon : ℝ} (hc : 0 ≤ c)
    (hB : 1 - mu.real B ≤ c * (n : ℝ) ^ (-epsilon)) :
    1 - c ^ ((1 : ℝ) / (2 * alpha ^ 3 : ℕ)) *
        (n : ℝ) ^ (-epsilon / (2 * alpha ^ 3 : ℕ)) ≤
      mu.real (bdcLongRectangleBaseEvent alpha n) := by
  apply bdcLongRectangle_polynomial_deficit mu hpa hshift ha hn hc
  exact bdcLongRectangleUnion_deficit_of_cover mu B hcover hB

end BeffaraDC
end StatMech
