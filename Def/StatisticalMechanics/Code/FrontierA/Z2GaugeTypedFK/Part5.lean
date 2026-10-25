/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part3
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def typedSignedCompatibleEquiv (ends : P -> V × V) (D : Finset P)
    (omega : P -> Bool) (witness : V -> Bool)
    (hw : TypedSignedCompatible ends D omega witness) :
    {sigma : V -> Bool // TypedSignedCompatible ends D omega sigma} ≃
      {tau : V -> Bool // TypedSignedCompatible ends ∅ omega tau} where
  toFun sigma := ⟨typedSpinXor sigma.1 witness, by
    intro p hp
    have hs := sigma.2 p hp
    have hwe := hw p hp
    have heq :
        (sigma.1 (ends p).1 = sigma.1 (ends p).2) <->
          (witness (ends p).1 = witness (ends p).2) :=
      hs.trans hwe.symm
    constructor
    · intro _
      simp
    · intro _
      exact (bool_xor_eq_xor_iff_eq_iff_eq
        (sigma.1 (ends p).1) (sigma.1 (ends p).2)
        (witness (ends p).1) (witness (ends p).2)).2 heq⟩
  invFun tau := ⟨typedSpinXor tau.1 witness, by
    intro p hp
    have ht : tau.1 (ends p).1 = tau.1 (ends p).2 :=
      (tau.2 p hp).2 (by simp)
    have hwe := hw p hp
    change
      ((tau.1 (ends p).1).xor (witness (ends p).1) =
        (tau.1 (ends p).2).xor (witness (ends p).2)) <-> p ∉ D
    rw [bool_xor_eq_xor_iff_eq_iff_eq]
    simpa [ht] using hwe⟩
  left_inv sigma := by
    apply Subtype.ext
    exact typedSpinXor_cancel_right sigma.1 witness
  right_inv tau := by
    apply Subtype.ext
    exact typedSpinXor_cancel_right tau.1 witness

end
end StatMech.FrontierA
