/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.BoxConnectionFullConnection
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4RadialDecay.Part4
open MeasureTheory SimpleGraph
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

abbrev fkQgt4CriticalFreeMeasure {q : Real} (hq : 4 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site 2))) :=
  FK.freeInfiniteVolume 2
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    (by linarith : (0 : Real) < q)


end
end StatMech.FrontierD
