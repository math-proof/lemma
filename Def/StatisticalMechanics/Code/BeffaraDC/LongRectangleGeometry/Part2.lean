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
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech

namespace BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


def bdcLongRectangleBaseEvent (alpha n : ℕ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  verticalCrossingEvent 0 (2 * (n : ℤ)) 0
    (2 * (alpha : ℤ) * (n : ℤ))


def bdcLongRectangleEvent (alpha n : ℕ)
    (k : BdcLongRectangleIndex alpha) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  verticalCrossingEvent
    (bdcLongRectangleXOffset n k : ℤ)
    ((bdcLongRectangleXOffset n k : ℤ) + 2 * (n : ℤ))
    (bdcLongRectangleYOffset n k : ℤ)
    ((bdcLongRectangleYOffset n k : ℤ) +
      2 * (alpha : ℤ) * (n : ℤ))


end BeffaraDC
end StatMech
