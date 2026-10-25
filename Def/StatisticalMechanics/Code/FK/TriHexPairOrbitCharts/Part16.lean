/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part13
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def triangularNonedgePairShapeEmbedding :
    Nat ↪ {s : TriangularPairShape // ¬ IsTriangularEdgePairShape s} where
  toFun n := ⟨triangularNonedgePairShape n,
    triangularNonedgePairShape_not_edge n⟩
  inj' _ _ h := triangularNonedgePairShape_injective
    (congrArg Subtype.val h)

def hexagonalNonedgePairShape (n : Nat) : HexagonalPairShape :=
  Sum.inl (⟨longPairDisplacement n, by
    left
    simp only [longPairDisplacement, Matrix.cons_val_zero]
    exact add_pos_of_nonneg_of_pos (Int.natCast_nonneg n) (by norm_num)⟩,
      false, false)

end StatMech.FK.PeriodicPlanar
