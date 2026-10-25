/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part4


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable def killedChoicePathFamilyHitNoHit
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogKilledChoicePathFamily R t p q →
      IsingLeapfrogKilledChoiceFirstHitFamily R t p q level ⊕
        IsingLeapfrogKilledChoiceNoHitFamily R t p q level := fun w => by
  let o := isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
    (isingLeapfrogChoiceSteps w.1)
  by_cases hnone : o = none
  · exact Sum.inr ⟨w, hnone⟩
  · have his : o.isSome = true :=
      Option.ne_none_iff_isSome.mp hnone
    exact Sum.inl ⟨⟨w, o.get his⟩, (Option.some_get his).symm⟩


noncomputable def killedChoicePathFamilyHitNoHitEquiv
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogKilledChoicePathFamily R t p q ≃
      IsingLeapfrogKilledChoiceFirstHitFamily R t p q level ⊕
        IsingLeapfrogKilledChoiceNoHitFamily R t p q level where
  toFun := killedChoicePathFamilyHitNoHit R t p q level
  invFun z := z.elim (fun w => w.1.1) (fun w => w.1)
  left_inv w := by
    unfold killedChoicePathFamilyHitNoHit
    dsimp only
    split <;> rfl
  right_inv z := by
    rcases z with w | w
    · unfold killedChoicePathFamilyHitNoHit
      dsimp only
      have hne : isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p)
          level (isingLeapfrogChoiceSteps w.1.1.1) ≠ none := by
        rw [w.2]
        simp
      simp [hne]
      congr 1
      apply Prod.ext
      · rfl
      · apply Option.some.inj
        rw [← w.2]
        exact Option.some_get _
    · unfold killedChoicePathFamilyHitNoHit
      dsimp only
      simp [w.2]

end
end StatMech.Universality
