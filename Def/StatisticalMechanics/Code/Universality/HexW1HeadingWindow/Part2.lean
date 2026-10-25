/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexW1HeadingWindow.Part3


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


noncomputable def hexW1_trivialWindingBound (a : ℂ) (h0 : ℤ) :
    HexWindingBound (fun m => m = a) a h0 a where
  H := h0
  w := h0
  hHL := le_refl _
  hHU := by omega
  sideExit := by
    intro ts hadm
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    rw [hexInfra_headAccum_nil]
    exact hexInfra_trivial_lastVertex a h0
  bound := by
    intro ts hadm
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    rw [hexInfra_headAccum_nil]
    norm_num


end StatMech.Universality
