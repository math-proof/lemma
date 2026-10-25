/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part4


namespace StatMech.FrontierD

noncomputable section

def fkMedialBlackDartMaskSwap {T : EvenTorus}
    (mask : T.Vertex -> Bool) : Equiv.Perm (FKMedialBlackDart T) where
  toFun dart := if mask dart.1.1 then
    fkMedialBlackDartSwap dart.1.1 dart else dart
  invFun dart := if mask dart.1.1 then
    fkMedialBlackDartSwap dart.1.1 dart else dart
  left_inv dart := by
    by_cases hmask : mask dart.1.1
    · simp only [hmask, if_true]
      rw [fkMedialBlackDartSwap_self_vertex, hmask]
      simp [fkMedialBlackDartSwap]
    · simp [hmask]
  right_inv dart := by
    by_cases hmask : mask dart.1.1
    · simp only [hmask, if_true]
      rw [fkMedialBlackDartSwap_self_vertex, hmask]
      simp [fkMedialBlackDartSwap]
    · simp [hmask]


def fkColoredParityMaskStrandSlotSwap {T : EvenTorus}
    (mask : T.Vertex -> Bool) (parity : Bool) :
    Equiv.Perm (T.Vertex × Bool) where
  toFun slot :=
    if mask slot.1 && (fkMedialVertexParity slot.1 == parity) then
      (slot.1, !slot.2)
    else slot
  invFun slot :=
    if mask slot.1 && (fkMedialVertexParity slot.1 == parity) then
      (slot.1, !slot.2)
    else slot
  left_inv slot := by
    rcases slot with ⟨v, side⟩
    cases h : mask v && (fkMedialVertexParity v == parity) <;>
      cases side <;> simp [h]
  right_inv slot := by
    rcases slot with ⟨v, side⟩
    cases h : mask v && (fkMedialVertexParity v == parity) <;>
      cases side <;> simp [h]

end
end StatMech.FrontierD
