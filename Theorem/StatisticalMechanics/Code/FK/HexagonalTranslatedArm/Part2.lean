module
public import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
public import Def.StatisticalMechanics.Code.FK.HexagonalTranslatedArm.Part2
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean -/
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

theorem hexagonalTransBoxToBuffered_injective (k : Nat) (x : Site 2) :
    Function.Injective (hexagonalTransBoxToBuffered k x) := by
  intro y z h
  apply Subtype.ext
  exact congrArg (fun w : hexagonal.BufferedVertex
    (hexagonalTransBufferLevel k x) => (w : HexVertex)) h

end StatMech.FK.PeriodicPlanar
