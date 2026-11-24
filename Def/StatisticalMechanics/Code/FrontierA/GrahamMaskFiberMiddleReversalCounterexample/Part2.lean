module
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamThreeGateBoundaryCounterexample.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversalCounterexample
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversalCounterexample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent


def canonicalGateCounterMaskProfile : Finset (Fin 21) × Finset (Fin 21) :=
  fourColorMaskProfile canonicalGateCounterSupport canonicalGateCounterColoring


def canonicalGateCounterSourcePoint :
    leftSourceMaskFiber canonicalGateCounterEnds canonicalGateCounterSupport
      0 1 2 3 canonicalGateCounterMaskProfile :=
  ⟨canonicalGateCounterColoring,
    canonicalGateCounterColoring_leftSourcePattern, rfl⟩

end StatMech.GrahamGHS.FourColor
