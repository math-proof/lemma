/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFourier
import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Instance.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


@[simp] theorem triangularTorusXSeamEdge_diagonal
    (L : Nat) (y : ZMod L) :
    triangularTorusXSeamEdge L
      s(((0 : ZMod L), y), (-1, y - 1)) :=
  Or.inr ⟨y, rfl⟩

@[simp] theorem triangularTorusYSeamEdge_diagonal
    (L : Nat) (x : ZMod L) :
    triangularTorusYSeamEdge L
      s((x, (0 : ZMod L)), (x - 1, -1)) :=
  Or.inr ⟨x, rfl⟩


end StatMech.FrontierA
