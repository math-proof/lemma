/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part16
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem hexagonalNonedgePairShape_not_edge (n : Nat) :
    ¬ IsHexagonalEdgePairShape (hexagonalNonedgePairShape n) := by
  rintro ⟨i, hi⟩
  have hc := congrArg (fun s : HexagonalPairShape =>
    match s with
    | Sum.inl d => d.2.2
    | Sum.inr _ => false) hi
  fin_cases i <;>
    simp [hexagonalNonedgePairShape, hexagonalEdgePairShape,
      hexagonalPairNormal, hexagonalStep, siteLexPositive,
      boolOrdered] at hc

theorem hexagonalNonedgePairShape_injective :
    Function.Injective hexagonalNonedgePairShape := by
  intro n m h
  have h0 := congrArg (fun s : HexagonalPairShape =>
    match s with
    | Sum.inl d => d.1.1 0
    | Sum.inr _ => 0) h
  simp [hexagonalNonedgePairShape, longPairDisplacement] at h0
  omega

end StatMech.FK.PeriodicPlanar
