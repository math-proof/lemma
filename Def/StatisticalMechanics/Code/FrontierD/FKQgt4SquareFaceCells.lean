module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part3
open Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceCells.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

def fkSquareInteriorFace (n : Nat) (f : Site 2) : Prop :=
  -(n : Int) <= f 0 ∧ f 0 < n ∧ -(n : Int) <= f 1 ∧ f 1 < n

end
end StatMech.FrontierD
