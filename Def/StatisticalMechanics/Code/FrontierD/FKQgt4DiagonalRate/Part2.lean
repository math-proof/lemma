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
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate
open MeasureTheory Filter Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

noncomputable def fkQgt4CriticalFreeExactDiagonalTwoPoint
    {q : Real} (hq : 4 < q) (n : Nat) : Real :=
  FK.infiniteTwoPointReal
    ((FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
    (origin 2) (fkQgt4ExactDiagonalSite n)

end
end StatMech.FrontierD
