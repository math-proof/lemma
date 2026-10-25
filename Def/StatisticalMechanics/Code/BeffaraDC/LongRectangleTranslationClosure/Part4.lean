/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Abbrev.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


def bdcLongRectangleTorusTranslatedEvent
    (L alpha n : ℕ)
    (j : BdcLongRectangleTorusTranslationIndex L alpha) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  translateConfig (bdcTorusCanonicalShift j.1) ⁻¹'
    bdcLongRectangleEvent alpha n j.2


def bdcLongRectangleTorusTranslationExpandedUnion
    (L alpha n : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ j : BdcLongRectangleTorusTranslationIndex L alpha,
    bdcLongRectangleTorusTranslatedEvent L alpha n j


end StatMech.BeffaraDC
