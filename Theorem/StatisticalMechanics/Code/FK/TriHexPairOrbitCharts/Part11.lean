/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part12
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triangularEdgePairShape_injective :
    Function.Injective triangularEdgePairShape := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [triangularEdgePairShape, triangularPairNormal,
      triangularStep, siteLexNonnegative] at hij ⊢
  all_goals
    have h := congrArg (fun s : TriangularPairShape => (s.1 0, s.1 1)) hij
    norm_num at h

theorem hexagonalEdgePairShape_injective :
    Function.Injective hexagonalEdgePairShape := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [hexagonalEdgePairShape, hexagonalPairNormal,
      hexagonalStep, siteLexPositive, boolOrdered] at hij ⊢
  all_goals
    have h := congrArg (fun s : HexagonalPairShape =>
      match s with
      | Sum.inl d => (d.1.1 0, d.1.1 1)
      | Sum.inr _ => (0, 0)) hij
    norm_num at h

end StatMech.FK.PeriodicPlanar
