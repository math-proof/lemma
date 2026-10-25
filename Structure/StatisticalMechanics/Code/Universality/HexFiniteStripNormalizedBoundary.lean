/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalization.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexStripInterior.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part2


namespace StatMech.Universality

open Complex HexWalk


namespace HexFiniteRegion

structure DirectedStartIncidence (R : HexFiniteRegion) (h0 : ℤ) where
  
  dregion : ℂ → ℤ → Prop
  
  project : ∀ m h, dregion m h → R.inRegion m
  
  walksInDirectedRegion : ∀ ts : List ℤ,
    (ofTurns R.start h0 ts).IsLegalSAW →
    (ofTurns R.start h0 ts).StaysIn R.inRegion →
    hexStripStaysInDir dregion R.start h0 ts
  
  start_exact : ∀ h : ℤ, dregion R.start h → halfStep h = halfStep h0


end HexFiniteRegion
end StatMech.Universality
