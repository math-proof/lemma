module
public import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleSqrtTrick
public import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
public import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry.Part4
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


def bdcLongRectangleOriginIndex (alpha : ℕ) (ha : 0 < alpha) :
    BdcLongRectangleIndex alpha :=
  (⟨0, by positivity⟩, ⟨0, ha⟩)

end BeffaraDC
end StatMech
