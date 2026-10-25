/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDualEvents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDualEvents.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC

noncomputable section

theorem fkSquareBox_eventProb_duality (n : Nat)
    (A : Set (ConfigSpace (Sym2 (FK.boxVerts 2 n))))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq).toMeasure A =
      fkSquareBoxFaithfulDualEventProb n hp hp1 hq A := by
  unfold fkSquareBoxFaithfulDualEventProb
  rw [fkSquareBox_fkPMF_eq_faithfulDualPMF n hp hp1 hq]


theorem fkSquareBox_eventProb_selfDual (n : Nat)
    (A : Set (ConfigSpace (Sym2 (FK.boxVerts 2 n))))
    {q : Real} (hq : 0 < q) :
    (FK.fkPMF (FK.boxGraph 2 n)
      (selfDualPoint_mem_Ioo hq).1 (selfDualPoint_mem_Ioo hq).2 hq).toMeasure A =
      fkSquareBoxFaithfulDualEventProb n
        (selfDualPoint_mem_Ioo hq).1 (selfDualPoint_mem_Ioo hq).2 hq A := by
  exact fkSquareBox_eventProb_duality n A
    (selfDualPoint_mem_Ioo hq).1 (selfDualPoint_mem_Ioo hq).2 hq

end
end StatMech.FrontierD
