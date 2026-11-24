module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part3
open Set SimpleGraph StatMech.Lattice


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectParityBit (n : Nat) : Bool := decide (n % 2 = 1)

end
end StatMech.FrontierD
