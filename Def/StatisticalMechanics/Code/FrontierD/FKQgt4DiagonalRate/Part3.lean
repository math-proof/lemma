/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiscontinuityAssembly.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionFKG
import Mathlib.Analysis.Subadditive
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate.Part2
open MeasureTheory Filter Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

noncomputable def fkQgt4CriticalFreeExactDiagonalRateLimit
    {q : Real} (hq : 4 < q) : Real :=
  (fkQgt4CriticalFreeExactDiagonalNegLog_subadditive hq).lim

end
end StatMech.FrontierD
