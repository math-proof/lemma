/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def natGradedPairFiberEquivSigma
    {A B : Type*} (gradeA : A → Nat) (gradeB : B → Nat)
    (total : Nat) :
    {pair : A × B // gradeA pair.1 + gradeB pair.2 = total} ≃
      Sigma fun k : Fin (total + 1) =>
        {pair : A × B //
          gradeA pair.1 = k.val ∧
            gradeB pair.2 = total - k.val} where
  toFun pair :=
    ⟨⟨gradeA pair.1.1, by omega⟩,
      ⟨pair.1, rfl, by
        have hgrade := pair.2
        dsimp
        omega⟩⟩
  invFun data := ⟨data.2.1, by
      rw [data.2.2.1, data.2.2.2]
      omega⟩
  left_inv pair := by
    apply Subtype.ext
    rfl
  right_inv data := by
    rcases data with ⟨k, ⟨pair, hleft, hright⟩⟩
    apply Sigma.ext
    · apply Fin.ext
      exact hleft
    · apply (Subtype.heq_iff_coe_eq (fun value => by
          change
            (gradeA value.1 = gradeA pair.1 ∧
                gradeB value.2 = total - gradeA pair.1) ↔
              (gradeA value.1 = k.val ∧
                gradeB value.2 = total - k.val)
          rw [hleft])).2
      rfl

def natGradedPairFiberAtEquivProd
    {A B : Type*} (gradeA : A → Nat) (gradeB : B → Nat)
    (total : Nat) (k : Fin (total + 1)) :
    {pair : A × B //
      gradeA pair.1 = k.val ∧ gradeB pair.2 = total - k.val} ≃
      {a : A // gradeA a = k.val} ×
        {b : B // gradeB b = total - k.val} where
  toFun pair := (⟨pair.1.1, pair.2.1⟩, ⟨pair.1.2, pair.2.2⟩)
  invFun pair := ⟨(pair.1.1, pair.2.1), pair.1.2, pair.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end StatMech.FrontierD
