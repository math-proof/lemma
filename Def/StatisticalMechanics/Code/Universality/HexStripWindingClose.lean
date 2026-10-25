/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripWinding.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexStripWindingClose.Part2


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


def hexUmlauf_stripWinding_of_band (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripBand inRegion a h0 z) :
    HexStripWinding inRegion a h0 z where
  H := B.H
  w := B.w
  hHL := B.hHL
  hHU := B.hHU
  window := fun ts hadm k hk => B.windowField ts hadm k hk

end StatMech.Universality
