/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDualEvents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDualEvents
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC

noncomputable section

@[simp] theorem fkSquareBoxFaithfulDualPMF_apply (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))) :
    fkSquareBoxFaithfulDualPMF n hp hp1 hq omega =
      ENNReal.ofReal
        (pfdDualProb (fkSquareBoxPlanar n) (dualParam p q) q omega) :=
  PMF.ofFintype_apply _ _


theorem fkSquareBox_fkPMF_eq_faithfulDualPMF (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq =
      fkSquareBoxFaithfulDualPMF n hp hp1 hq := by
  ext omega
  rw [FK.fkPMF_apply, fkSquareBoxFaithfulDualPMF_apply,
    fkSquareBox_fkProb_duality n omega hp hp1 hq]


end
end StatMech.FrontierD
