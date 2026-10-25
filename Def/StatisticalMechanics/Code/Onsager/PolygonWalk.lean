/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Abbrev.StatisticalMechanics.Code.Onsager.PolygonWalk


namespace StatMech.Onsager.PolygonWalk

def cross (a b : Pt) : ℤ := a.1 * b.2 - a.2 * b.1


def isUnitDir (d : Pt) : Prop := d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)


end StatMech.Onsager.PolygonWalk
