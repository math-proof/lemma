/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part16
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


noncomputable def triHexPairOrbitDataEquiv :
    (Site 2 × TriangularPairShape) ≃
      (Site 2 × HexagonalPairShape) where
  toFun a := (a.1 + triHexPairShapeOffset a.2,
    triHexPairShapeEquiv a.2)
  invFun b :=
    (b.1 - triHexPairShapeOffset (triHexPairShapeEquiv.symm b.2),
      triHexPairShapeEquiv.symm b.2)
  left_inv a := by
    rcases a with ⟨x, s⟩
    simp
  right_inv b := by
    rcases b with ⟨x, s⟩
    simp


noncomputable def triHexFullDualEdgeEquiv :
    Sym2 (Site 2) ≃ Sym2 HexVertex :=
  triangularPairOrbitEquiv.trans
    (triHexPairOrbitDataEquiv.trans hexagonalPairOrbitEquiv.symm)

end StatMech.FK.PeriodicPlanar
