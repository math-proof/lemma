/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFourier
import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Instance.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


def triangularTorusXSeamEdge (L : Nat)
    (edge : Sym2 (ZMod L × ZMod L)) : Prop :=
  ons_xSeamEdge L edge ∨
    ∃ y : ZMod L, edge = s(((0 : ZMod L), y), (-1, y - 1))


def triangularTorusYSeamEdge (L : Nat)
    (edge : Sym2 (ZMod L × ZMod L)) : Prop :=
  ons_ySeamEdge L edge ∨
    ∃ x : ZMod L, edge = s((x, (0 : ZMod L)), (x - 1, -1))

end StatMech.FrontierA
