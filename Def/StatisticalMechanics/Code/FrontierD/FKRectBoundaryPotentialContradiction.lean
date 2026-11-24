module
public import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusComplementPotential.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedConnectedInsertionCarrier


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryPotentialContradiction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open IntegralSquareTorusCycle

open Finset SimpleGraph

noncomputable section

def fkRectRepeatDartList {alpha : Type*} : Nat → List alpha → List alpha
  | 0, _ => []
  | n + 1, l => l ++ fkRectRepeatDartList n l

end
end StatMech.FrontierD
