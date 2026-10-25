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
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry.Part2
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


theorem bdcLongRectangleEvent_eq_preimage (alpha n : ℕ)
    (k : BdcLongRectangleIndex alpha) :
    bdcLongRectangleEvent alpha n k =
      translateConfig (bdcLongRectangleShift n k) ⁻¹'
        bdcLongRectangleBaseEvent alpha n := by
  simpa [bdcLongRectangleEvent, bdcLongRectangleBaseEvent, add_comm,
    bdcLongRectangleShift] using
    (cti_verticalCrossingEvent_translate 0 (2 * (n : ℤ)) 0
      (2 * (alpha : ℤ) * (n : ℤ))
      (bdcLongRectangleShift n k))


theorem bdcLongRectangleEvent_isIncreasing (alpha n : ℕ)
    (k : BdcLongRectangleIndex alpha) :
    IsIncreasing (bdcLongRectangleEvent alpha n k) := by
  exact verticalCrossingEvent_isIncreasing _ _ _ _


theorem bdcLongRectangleEvent_measurableSet (alpha n : ℕ)
    (k : BdcLongRectangleIndex alpha) :
    MeasurableSet (bdcLongRectangleEvent alpha n k) := by
  exact rlc_verticalCrossing_measurableSet _ _ _ _


theorem bdcLongRectangleBaseEvent_measurableSet (alpha n : ℕ) :
    MeasurableSet (bdcLongRectangleBaseEvent alpha n) := by
  exact rlc_verticalCrossing_measurableSet _ _ _ _


theorem bdcLongRectangleEvent_probability_eq
    (mu : Measure (ConfigSpace (Sym2 (Site 2))))
    (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu)
    (alpha n : ℕ) (k : BdcLongRectangleIndex alpha) :
    mu.real (bdcLongRectangleEvent alpha n k) =
      mu.real (bdcLongRectangleBaseEvent alpha n) := by
  rw [bdcLongRectangleEvent_eq_preimage]
  exact (hshift (bdcLongRectangleShift n k)).measureReal_preimage
    (bdcLongRectangleBaseEvent_measurableSet alpha n).nullMeasurableSet


theorem bdcLongRectangleEvent_pairwise_probability_eq
    (mu : Measure (ConfigSpace (Sym2 (Site 2))))
    (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu)
    (alpha n : ℕ) (k l : BdcLongRectangleIndex alpha) :
    mu.real (bdcLongRectangleEvent alpha n k) =
      mu.real (bdcLongRectangleEvent alpha n l) := by
  calc
    mu.real (bdcLongRectangleEvent alpha n k) =
        mu.real (bdcLongRectangleBaseEvent alpha n) :=
      bdcLongRectangleEvent_probability_eq mu hshift alpha n k
    _ = mu.real (bdcLongRectangleEvent alpha n l) :=
      (bdcLongRectangleEvent_probability_eq mu hshift alpha n l).symm


theorem bdcLongRectangleEvent_probability_eq_selfDual
    (alpha n : ℕ) (k : BdcLongRectangleIndex alpha) :
    rba_selfDualMeasure.real (bdcLongRectangleEvent alpha n k) =
      rba_selfDualMeasure.real (bdcLongRectangleBaseEvent alpha n) := by
  exact bdcLongRectangleEvent_probability_eq rba_selfDualMeasure
    cti_selfDual_shift_invariant alpha n k


end BeffaraDC
end StatMech
