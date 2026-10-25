/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def killedChoiceNoHitFiberEquiv
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    {w : IsingLeapfrogKilledChoiceNoHitAll R t p level //
      isingLeapfrogChoiceRun R p w.1.1 = q} ≃
        IsingLeapfrogKilledChoiceNoHitFamily R t p q level where
  toFun w := ⟨⟨w.1.1.1, w.1.1.2.1, w.1.1.2.2, w.2⟩, w.1.2⟩
  invFun w := ⟨⟨⟨w.1.1, w.1.2.1, w.1.2.2.1⟩, w.2⟩, w.1.2.2.2⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

noncomputable def killedChoiceNoHitAllEquivSigma
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogKilledChoiceNoHitAll R t p level ≃
      Σ q : IsingLeapfrogBox R,
        IsingLeapfrogKilledChoiceNoHitFamily R t p q level :=
  (Equiv.sigmaFiberEquiv (fun w : IsingLeapfrogKilledChoiceNoHitAll R t p
    level => isingLeapfrogChoiceRun R p w.1.1)).symm |>.trans
      (Equiv.sigmaCongrRight
        (fun q => killedChoiceNoHitFiberEquiv R t p q level))

end
end StatMech.Universality
