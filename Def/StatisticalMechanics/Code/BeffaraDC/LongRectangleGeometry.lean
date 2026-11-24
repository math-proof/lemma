module
public import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleSqrtTrick
public import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
public import Abbrev.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry
open MeasureTheory Set
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


def bdcLongRectanglePeriod (alpha n : ℕ) : ℕ :=
  2 * alpha ^ 2 * n


def bdcLongRectangleXOffset {alpha : ℕ} (n : ℕ)
    (k : BdcLongRectangleIndex alpha) : ℕ :=
  k.1.val * n


def bdcLongRectangleYOffset {alpha : ℕ} (n : ℕ)
    (k : BdcLongRectangleIndex alpha) : ℕ :=
  k.2.val * (2 * alpha * n)


def bdcLongRectangleShift {alpha : ℕ} (n : ℕ)
    (k : BdcLongRectangleIndex alpha) : Site 2 :=
  ![(bdcLongRectangleXOffset n k : ℤ),
    (bdcLongRectangleYOffset n k : ℤ)]


end BeffaraDC
end StatMech
