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
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexMarkedSectorRowCycleEquivVerticalTransitions
    (T : EvenTorus) (sector : Fin (T.width + 1)) :
    SixVertexMarkedSectorRowCycle T sector ≃
      Sigma fun vertical : SixVertexVerticalRowsInSector T sector =>
        forall j, SixVertexHorizontalTransitionWitness vertical.1 j where
  toFun rows :=
    ⟨⟨rows.1.2, rows.2.2⟩, fun j => ⟨rows.1.1 j, rows.2.1 j⟩⟩
  invFun data :=
    ⟨(fun j => (data.2 j).1, data.1.1),
      (fun j => (data.2 j).2), data.1.2⟩
  left_inv rows := by
    apply Subtype.ext
    apply Prod.ext <;> funext j <;> rfl
  right_inv data := by
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · rfl

def sixVertexVerticalRowsTotalC
    {T : EvenTorus} (vertical : Fin T.height → SixVertexRow T.width) : Nat :=
  ∑ j, sixVertexRowDistance
    (vertical (SixVertexArrows.cyclicPred T.height_pos j)) (vertical j)


def sixVertexMarkedSectorRowCycleGradeCount
    (T : EvenTorus) (sector : Fin (T.width + 1)) (totalC : Nat) : Nat :=
  ∑ vertical : SixVertexVerticalRowsInSector T sector,
    if sixVertexVerticalRowsTotalC vertical.1 = totalC then
      ∏ j, Fintype.card
        (SixVertexHorizontalTransitionWitness vertical.1 j)
    else 0

def sigmaSubtypeBaseComm {A : Type*} (B : A → Type*) (p : A → Prop) :
    (Sigma fun a : Subtype p => B a.1) ≃
      Sigma fun a : A => {_b : B a // p a} where
  toFun value := ⟨value.1.1, ⟨value.2, value.1.2⟩⟩
  invFun value := ⟨⟨value.1, value.2.2⟩, value.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

def subtypeSigmaBaseEquiv
    {X A : Type*} (B : A → Type*) (equiv : X ≃ Sigma B)
    (sourcePred : X → Prop) (basePred : A → Prop)
    (hpred : forall value, sourcePred value ↔ basePred (equiv value).1) :
    {value : X // sourcePred value} ≃
      Sigma fun a : A => {_b : B a // basePred a} :=
  (Equiv.subtypeEquiv equiv hpred).trans
    ((Equiv.subtypeSigmaEquiv B basePred).trans
      (sigmaSubtypeBaseComm B basePred))

def sixVertexMarkedSectorRowCycleGradeFiberEquiv
    (T : EvenTorus) (sector : Fin (T.width + 1)) (totalC : Nat) :
    {rows : SixVertexMarkedSectorRowCycle T sector //
      sixVertexMarkedSectorRowCycleTotalC rows = totalC} ≃
      Sigma fun vertical : SixVertexVerticalRowsInSector T sector =>
        {_witness : forall j,
            SixVertexHorizontalTransitionWitness vertical.1 j //
          sixVertexVerticalRowsTotalC vertical.1 = totalC} where
  toFun :=
    ((Equiv.subtypeEquiv
      (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T sector)
      (fun _ => Iff.rfl)).trans
        ((Equiv.subtypeSigmaEquiv
          (fun vertical : SixVertexVerticalRowsInSector T sector =>
            forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
          (fun vertical =>
            sixVertexVerticalRowsTotalC vertical.1 = totalC)).trans
          (sigmaSubtypeBaseComm
            (fun vertical : SixVertexVerticalRowsInSector T sector =>
              forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
            (fun vertical =>
              sixVertexVerticalRowsTotalC vertical.1 = totalC)))).toFun
  invFun :=
    ((Equiv.subtypeEquiv
      (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T sector)
      (fun _ => Iff.rfl)).trans
        ((Equiv.subtypeSigmaEquiv
          (fun vertical : SixVertexVerticalRowsInSector T sector =>
            forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
          (fun vertical =>
            sixVertexVerticalRowsTotalC vertical.1 = totalC)).trans
          (sigmaSubtypeBaseComm
            (fun vertical : SixVertexVerticalRowsInSector T sector =>
              forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
            (fun vertical =>
              sixVertexVerticalRowsTotalC vertical.1 = totalC)))).invFun
  left_inv := ((Equiv.subtypeEquiv
      (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T sector)
      (fun _ => Iff.rfl)).trans
        ((Equiv.subtypeSigmaEquiv
          (fun vertical : SixVertexVerticalRowsInSector T sector =>
            forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
          (fun vertical =>
            sixVertexVerticalRowsTotalC vertical.1 = totalC)).trans
          (sigmaSubtypeBaseComm
            (fun vertical : SixVertexVerticalRowsInSector T sector =>
              forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
            (fun vertical =>
              sixVertexVerticalRowsTotalC vertical.1 = totalC)))).left_inv
  right_inv := ((Equiv.subtypeEquiv
      (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T sector)
      (fun _ => Iff.rfl)).trans
        ((Equiv.subtypeSigmaEquiv
          (fun vertical : SixVertexVerticalRowsInSector T sector =>
            forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
          (fun vertical =>
            sixVertexVerticalRowsTotalC vertical.1 = totalC)).trans
          (sigmaSubtypeBaseComm
            (fun vertical : SixVertexVerticalRowsInSector T sector =>
              forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
            (fun vertical =>
              sixVertexVerticalRowsTotalC vertical.1 = totalC)))).right_inv

end
end StatMech.FrontierD
