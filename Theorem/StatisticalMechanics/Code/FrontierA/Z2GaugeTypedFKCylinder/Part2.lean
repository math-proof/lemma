/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part14
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugePerimeterReduction.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part2
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem cubicalXYSheet_subset_belowCut
    {a b c : Nat} (k : Fin (c + 1)) (hk : 0 < k.val) :
    cubicalXYSheet (a := a) (b := b) k ⊆
      multibondCut (cubicalDualEnds (a := a) (b := b) (c := c))
        (cubicalBelowSpin (a := a) (b := b) k) := by
  intro p hp
  obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hp
  rw [mem_multibondCut]
  cases hback : finBackward k with
  | none =>
      have hk0 : k = 0 := (finBackward_eq_none_iff k).mp hback
      exfalso
      rw [hk0] at hk
      simp at hk
  | some z =>
      have hkz : k = z.succ := (finBackward_eq_some_iff k z).mp hback
      have hz : z.val < k.val := by rw [hkz]; simp
      rw [cubicalDualEnds, hback]
      cases hforward : finForward k with
      | none => simp [cubicalBelowSpin, hz]
      | some w =>
          have heq : k = w.castSucc :=
            (finForward_eq_some_iff k w).mp hforward
          have hw : ¬ w.val < k.val := by rw [heq]; simp
          simp [cubicalBelowSpin, hz, hw]


end
end StatMech.FrontierA
