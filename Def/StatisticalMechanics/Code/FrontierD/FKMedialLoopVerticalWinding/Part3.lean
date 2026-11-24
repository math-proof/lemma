module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part2
open Equiv Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}


def fkMedialDownwardVerticalMode
    (pairing : FKMedialLoopPairing T) (C : FKMedialLoop T pairing) : Bool :=
  decide (0 ≤ fkMedialLoopCanonicalVerticalFlux pairing C)

end
end StatMech.FrontierD
