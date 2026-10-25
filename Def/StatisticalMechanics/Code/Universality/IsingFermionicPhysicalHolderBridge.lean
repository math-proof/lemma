/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalHolderBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDeepEnergy.Part4


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable def fkIsingSquareRadialPatchDeepVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (base : Real) : Real :=
  (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
      |fkIsingSquareRadialPatchPrimalValue
          n m hn hm (by omega) base d.snd -
        fkIsingSquareRadialPatchPrimalValue
          n m hn hm (by omega) base d.fst|) +
    ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
      |fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base d.snd -
        fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base d.fst|

end
end StatMech.Universality
