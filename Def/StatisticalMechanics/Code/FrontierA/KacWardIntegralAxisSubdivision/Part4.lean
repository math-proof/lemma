module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForwardSubdivision
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open Set

open scoped BigOperators

open StatMech.Onsager.BaseCase


def kwIntegralPolygonEdgePoints
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n) :
    List (ℤ × ℤ) :=
  (kwPrefixPositions (kwIntegralPolygonEdgeWord p i)).map (p i + ·)

end StatMech.FrontierA
