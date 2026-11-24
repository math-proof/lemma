module
public import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalization.Part2
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
public import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
public import Theorem.StatisticalMechanics.Code.Universality.HexStripInterior.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex HexWalk


namespace HexFiniteRegion

def StartInteriorUnique (R : HexFiniteRegion) (h0 : ℤ) : Prop :=
  ∀ h : ℤ, R.start + halfStep h ∈ R.verts →
    R.start + halfStep h = R.start + halfStep h0


end HexFiniteRegion
end StatMech.Universality
