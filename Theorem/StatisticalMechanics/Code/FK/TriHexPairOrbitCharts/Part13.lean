/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part15
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triangularNonedgePairShape_not_edge (n : Nat) :
    ¬ IsTriangularEdgePairShape (triangularNonedgePairShape n) := by
  rintro ⟨i, hi⟩
  fin_cases i <;>
    have h0 := congrArg (fun s : TriangularPairShape => s.1 0) hi <;>
    simp [triangularNonedgePairShape, longPairDisplacement,
      triangularEdgePairShape, triangularPairNormal,
      triangularStep, siteLexNonnegative] at h0
  all_goals have hn : (0 : Int) <= n := Int.natCast_nonneg n
  all_goals omega

theorem triangularNonedgePairShape_injective :
    Function.Injective triangularNonedgePairShape := by
  intro n m h
  have h0 := congrArg (fun s : TriangularPairShape => s.1 0) h
  simp [triangularNonedgePairShape, longPairDisplacement] at h0
  omega

end StatMech.FK.PeriodicPlanar
