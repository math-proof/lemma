module
public import Theorem.StatisticalMechanics.Code.FK.BoxConnectionFullConnection
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4RadialDecay.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTwoPointComparison.Part2
open MeasureTheory SimpleGraph
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

noncomputable def fkRectHorizontalCylinderCorrectionFloor
    {q : Real} (hq : 4 < q) (width : Nat) : Real :=
  ∏ dx ∈ Finset.Icc (-(width : Int)) (width : Int),
    fkQgt4CriticalFreeTwoPoint hq
      (fkRectHorizontalCylinderCorrection dx)

end
end StatMech.FrontierD
