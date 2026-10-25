/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


def hexIncident (v m : ℂ) (d : ℤ) : Prop :=
  v = m + HexWalk.halfStep d ∨ v = m + HexWalk.halfStep (d + 3)


def hexStripInterior (dregion : ℂ → ℤ → Prop) (v : ℂ) : Prop :=
  ∃ (m1 m2 : ℂ) (d1 d2 : ℤ), dregion m1 d1 ∧ dregion m2 d2 ∧ (m1, d1) ≠ (m2, d2)
    ∧ hexIncident v m1 d1 ∧ hexIncident v m2 d2


noncomputable def hexStripDirMids (m : ℂ) (h : ℤ) : List ℤ → List (ℂ × ℤ)
  | [] => [(m, h)]
  | t :: ts =>
      (m, h) :: hexStripDirMids (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) ts

end StatMech.Universality
