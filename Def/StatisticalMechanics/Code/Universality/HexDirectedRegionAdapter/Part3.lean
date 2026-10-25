/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexDirectedRegionAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexDirectedRegionAdapter.Part2


namespace StatMech.Universality

open Complex HexWalk


def hexStripInteriorDistinctMidpoint (dregion : ℂ → ℤ → Prop)
    (v : ℂ) : Prop :=
  ∃ (m1 m2 : ℂ) (d1 d2 : ℤ),
    dregion m1 d1 ∧ dregion m2 d2 ∧ m1 ≠ m2
      ∧ hexIncident v m1 d1 ∧ hexIncident v m2 d2


end StatMech.Universality
