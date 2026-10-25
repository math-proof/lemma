/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure.Part5
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem bdcLongRectangleTorusTranslationIndices_card
    (L alpha : ℕ) [NeZero L] :
    (bdcLongRectangleTorusTranslationIndices L alpha).card =
      L ^ 2 * (2 * alpha ^ 3) := by
  simpa [bdcLongRectangleTorusTranslationIndices] using
    bdcLongRectangleTorusTranslationIndex_card L alpha


theorem monotone_translateConfig (t : Site 2) :
    Monotone (translateConfig t) := by
  intro omega eta homega e
  exact homega _


theorem bdcLongRectangleTorusTranslatedEvent_isIncreasing
    (L alpha n : ℕ)
    (j : BdcLongRectangleTorusTranslationIndex L alpha) :
    IsIncreasing (bdcLongRectangleTorusTranslatedEvent L alpha n j) := by
  intro omega eta homegaeta homega
  exact bdcLongRectangleEvent_isIncreasing alpha n j.2
    (monotone_translateConfig (bdcTorusCanonicalShift j.1) homegaeta)
    homega


theorem bdcLongRectangleTorusTranslatedEvent_measurableSet
    (L alpha n : ℕ)
    (j : BdcLongRectangleTorusTranslationIndex L alpha) :
    MeasurableSet (bdcLongRectangleTorusTranslatedEvent L alpha n j) := by
  exact (bdcLongRectangleEvent_measurableSet alpha n j.2).preimage
    (cti_measurable_translateConfig (bdcTorusCanonicalShift j.1))


theorem bdcLongRectangleTorusTranslatedEvent_probability_eq
    (mu : Measure (ConfigSpace (Sym2 (Site 2))))
    (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu)
    (L alpha n : ℕ)
    (j : BdcLongRectangleTorusTranslationIndex L alpha) :
    mu.real (bdcLongRectangleTorusTranslatedEvent L alpha n j) =
      mu.real (bdcLongRectangleBaseEvent alpha n) := by
  calc
    mu.real (bdcLongRectangleTorusTranslatedEvent L alpha n j) =
        mu.real (bdcLongRectangleEvent alpha n j.2) :=
      (hshift (bdcTorusCanonicalShift j.1)).measureReal_preimage
        (bdcLongRectangleEvent_measurableSet alpha n j.2).nullMeasurableSet
    _ = mu.real (bdcLongRectangleBaseEvent alpha n) :=
      bdcLongRectangleEvent_probability_eq mu hshift alpha n j.2


theorem bdcLongRectangleTorusTranslationExpandedUnion_eq_finset
    (L alpha n : ℕ) [NeZero L] :
    bdcLongRectangleTorusTranslationExpandedUnion L alpha n =
      ⋃ j ∈ bdcLongRectangleTorusTranslationIndices L alpha,
        bdcLongRectangleTorusTranslatedEvent L alpha n j := by
  ext omega
  simp [bdcLongRectangleTorusTranslationExpandedUnion,
    bdcLongRectangleTorusTranslationIndices]


end StatMech.BeffaraDC
