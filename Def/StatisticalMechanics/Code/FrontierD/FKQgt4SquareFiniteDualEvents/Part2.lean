/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDualEvents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDualEvents
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC

noncomputable section

noncomputable def fkSquareBoxFaithfulDualEventProb (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 (FK.boxVerts 2 n)))) : ENNReal :=
  (fkSquareBoxFaithfulDualPMF n hp hp1 hq).toMeasure A


end
end StatMech.FrontierD
