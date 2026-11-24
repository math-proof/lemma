module
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossing.Part6
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCounterexample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.BeffaraDC

open StatMech.Onsager


noncomputable def torusSquareShiftCounterexampleConfig
    (L : ℕ) [Fact (2 < L)] : TorusAmbientConfig L :=
  fun e => decide (e = torusHorizontalEdge L 0 0)

end StatMech.BeffaraDC
