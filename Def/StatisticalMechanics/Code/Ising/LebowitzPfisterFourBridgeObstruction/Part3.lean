module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeClosure
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterStrongMarkedSite
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeObstruction.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

def fourBridgeRankMass (a b c d : Real) : Fin 5 -> Real
  | 0 => (1 - a + b - c + d) / 16
  | 1 => (4 - 2 * a + 2 * c - 4 * d) / 16
  | 2 => (6 - 2 * b + 6 * d) / 16
  | 3 => (4 + 2 * a - 2 * c - 4 * d) / 16
  | 4 => (1 + a + b + c + d) / 16


end
end StatMech.Ising
