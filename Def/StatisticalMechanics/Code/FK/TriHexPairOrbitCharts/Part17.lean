/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part14
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def hexagonalNonedgePairShapeEmbedding :
    Nat ↪ {s : HexagonalPairShape // ¬ IsHexagonalEdgePairShape s} where
  toFun n := ⟨hexagonalNonedgePairShape n,
    hexagonalNonedgePairShape_not_edge n⟩
  inj' _ _ h := hexagonalNonedgePairShape_injective
    (congrArg Subtype.val h)

noncomputable def triHexNonedgePairShapeEquiv :
    {s : TriangularPairShape // ¬ IsTriangularEdgePairShape s} ≃
      {s : HexagonalPairShape // ¬ IsHexagonalEdgePairShape s} := by
  letI : Infinite
      {s : TriangularPairShape // ¬ IsTriangularEdgePairShape s} :=
    Infinite.of_injective _ triangularNonedgePairShapeEmbedding.injective
  letI : Infinite
      {s : HexagonalPairShape // ¬ IsHexagonalEdgePairShape s} :=
    Infinite.of_injective _ hexagonalNonedgePairShapeEmbedding.injective
  exact Classical.choice inferInstance


noncomputable def triHexPairShapeEquiv :
    TriangularPairShape ≃ HexagonalPairShape :=
  (Equiv.sumCompl IsTriangularEdgePairShape).symm |>.trans
    (((triangularEdgePairShapeEquiv.symm.trans
        hexagonalEdgePairShapeEquiv).sumCongr
      triHexNonedgePairShapeEquiv).trans
    (Equiv.sumCompl IsHexagonalEdgePairShape))

end StatMech.FK.PeriodicPlanar
