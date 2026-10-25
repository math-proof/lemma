/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForwardSubdivision
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part4


namespace StatMech.FrontierA

open Set

open scoped BigOperators

open StatMech.Onsager.BaseCase


def kwIntegralPolygonPointList
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) : List (ℤ × ℤ) :=
  (List.ofFn (kwIntegralPolygonEdgePoints p)).flatten


def kwIndexedPrefixBlocks
    (start : ℕ → ℤ × ℤ) (blocks : List (List (Fin 4))) :
    List (ℤ × ℤ) :=
  (blocks.mapIdx fun k word ↦
    (kwPrefixPositions word).map (start k + ·)).flatten


end StatMech.FrontierA
