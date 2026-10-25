/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.BoxConnectionFullConnection
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4RadialDecay.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTwoPointComparison.Part3
open MeasureTheory SimpleGraph
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

noncomputable def fkRectHorizontalCylinderTwoPointFactor
    {q : Real} (hq : 4 < q) (width : Nat) : Real :=
  (fkRectHorizontalCylinderCorrectionFloor hq width)⁻¹

end
end StatMech.FrontierD
