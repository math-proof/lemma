module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
public import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareDirichletConvergence
open Finset SimpleGraph Filter Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareBoxQuadraticBarrier
    (n : Nat) (x : (fkSquareBoxPlanar n).V) : Real :=
  (2 * (n : Real) ^ 2 - (x.1 0 : Real) ^ 2 -
    (x.1 1 : Real) ^ 2) / 4

end
end StatMech.Universality
