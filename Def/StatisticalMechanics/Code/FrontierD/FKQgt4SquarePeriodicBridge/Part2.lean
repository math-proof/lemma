/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part12
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicBridge.Part2
open Finset SimpleGraph MeasureTheory


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK StatMech.FK.PeriodicPlanar

noncomputable section

noncomputable def fkSquarePeriodicConfigEquiv (n : Nat) :
    ConfigSpace (Sym2 (FK.boxVerts 2 n)) ≃
      ConfigSpace (Sym2 (square.OrbitVertex n)) :=
  FK.reCfgIsoEquiv (fkSquarePeriodicVertexEquiv n)

end
end StatMech.FrontierD
