/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Structure.StatisticalMechanics.Code.Universality.HexReturnUniqueness


namespace StatMech.Universality

open Complex HexWalk


namespace HexReturnCoord

noncomputable def value (d : HexReturnCoord) : ℂ :=
  (d.x : ℂ) + (d.y : ℂ) * hexOmega


def zero : HexReturnCoord := ⟨0, 0⟩


def base : HexReturnCoord := ⟨1, 0⟩


def negBase : HexReturnCoord := ⟨-1, 0⟩


def add (d e : HexReturnCoord) : HexReturnCoord := ⟨d.x + e.x, d.y + e.y⟩


def left (d : HexReturnCoord) : HexReturnCoord := ⟨d.x - d.y, d.x⟩


def right (d : HexReturnCoord) : HexReturnCoord := ⟨d.y, d.y - d.x⟩


def turn (d : HexReturnCoord) (t : ℤ) : HexReturnCoord :=
  if t = 1 then d.left else d.right

end HexReturnCoord
end StatMech.Universality
