module
public import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
public import Theorem.StatisticalMechanics.Code.FK.HexagonalTranslatedArm.Part4
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
public import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
public import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessCritical.Part3
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


noncomputable def hexagonalRootFrame : HexVertex ≃ HexVertex where
  toFun v := if hexagonal.root.2 then hexagonalReflect v else v
  invFun v := if hexagonal.root.2 then hexagonalReflect v else v
  left_inv v := by
    by_cases h : hexagonal.root.2 <;>
      simp [h, hexagonalReflect]
  right_inv v := by
    by_cases h : hexagonal.root.2 <;>
      simp [h, hexagonalReflect]

end StatMech.FK.PeriodicPlanar
