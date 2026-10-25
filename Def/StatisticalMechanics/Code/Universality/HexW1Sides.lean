/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1Sides.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexConnClosed
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part2


namespace StatMech.Universality

open HexWalk List Complex Filter Topology

open scoped BigOperators Real Topology


noncomputable def hexW1_trivialSide (a : ℂ) (h0 : ℤ) :
    HexBoundarySide (fun m => m = a) a h0 a where
  H := h0
  w := h0
  hHL := le_refl _
  hHU := by omega
  exits := by
    intro ts hadm
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    rw [hexInfra_headAccum_nil]
    exact ⟨by rw [hexInfra_midAccum_nil], le_refl _, by omega⟩


end StatMech.Universality
