/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexAWLong (c : HexAWCoord) : ℤ := c.i + c.j


def hexAWTrans (c : HexAWCoord) : ℤ := c.i - c.j


def hexAWDepth (c : HexAWCoord) : ℤ := -hexAWLong c


def hexAWBookRe2 (c : HexAWCoord) : ℤ :=
  3 * hexAWDepth c + match c.color with
    | .black => 1
    | .white => -1


def hexAWBookSqrt3Im2 (c : HexAWCoord) : ℤ := 3 * hexAWTrans c


def hexAWInStrip (T L : ℕ) (c : HexAWCoord) : Prop :=
  0 ≤ hexAWBookRe2 c ∧ hexAWBookRe2 c ≤ 3 * T ∧
  -((6 * L : ℕ) : ℤ) - hexAWBookRe2 c ≤ hexAWBookSqrt3Im2 c ∧
  hexAWBookSqrt3Im2 c ≤ (6 * L : ℕ) + hexAWBookRe2 c

end
end StatMech.Universality
