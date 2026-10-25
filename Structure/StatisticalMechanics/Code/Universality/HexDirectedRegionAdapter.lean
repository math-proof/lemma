/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexDirectedRegionAdapter.Part4


namespace StatMech.Universality

open Complex HexWalk


structure HexStripDirectedStartData
    (M : Finset ℂ) (a : ℂ) (h0 : ℤ) where
  
  dregion : ℂ → ℤ → Prop
  
  project : ∀ m h, dregion m h → m ∈ M
  
  launch : dregion a h0
  
  uniqueInterior : ∀ h : ℤ,
    hexStripInteriorDistinctMidpoint dregion (a + halfStep h) →
      halfStep h = halfStep h0

end StatMech.Universality
