module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiscontinuityAssembly.Part3
public import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionFKG
public import Mathlib.Analysis.Subadditive
open MeasureTheory Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

def fkQgt4ExactDiagonalSite (n : Nat) : Site 2 :=
  fun _ => (n : Int)

end
end StatMech.FrontierD
