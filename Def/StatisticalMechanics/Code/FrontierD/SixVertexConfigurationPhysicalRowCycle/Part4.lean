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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

def sigmaProdSigmaEquiv {A B : Type*} (F : A → Type*) (G : B → Type*) :
    (Sigma F × Sigma G) ≃
      Sigma fun pair : A × B => F pair.1 × G pair.2 where
  toFun value := ⟨(value.1.1, value.2.1), (value.1.2, value.2.2)⟩
  invFun value := (⟨value.1.1, value.2.1⟩, ⟨value.1.2, value.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

def sixVertexMarkedSectorRowCyclePairEquivVerticalTransitions
    (T : EvenTorus) (left right : Fin (T.width + 1)) :
    (SixVertexMarkedSectorRowCycle T left ×
      SixVertexMarkedSectorRowCycle T right) ≃
      Sigma fun vertical :
          SixVertexVerticalRowsInSector T left ×
            SixVertexVerticalRowsInSector T right =>
        ((forall j,
            SixVertexHorizontalTransitionWitness vertical.1.1 j) ×
          (forall j,
            SixVertexHorizontalTransitionWitness vertical.2.1 j)) :=
  (Equiv.prodCongr
    (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T left)
    (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T right)).trans
      (sigmaProdSigmaEquiv _ _)

def sixVertexMarkedSectorRowCyclePairTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorRowCycle T left ×
      SixVertexMarkedSectorRowCycle T right) : Nat :=
  sixVertexMarkedSectorRowCycleTotalC pair.1 +
    sixVertexMarkedSectorRowCycleTotalC pair.2

def sixVertexMarkedSectorRowCyclePairGradeCount
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (totalC : Nat) : Nat :=
  ∑ vertical : SixVertexVerticalRowsInSector T left ×
      SixVertexVerticalRowsInSector T right,
    if sixVertexVerticalRowsTotalC vertical.1.1 +
        sixVertexVerticalRowsTotalC vertical.2.1 = totalC then
      (∏ j, Fintype.card
        (SixVertexHorizontalTransitionWitness vertical.1.1 j)) *
      (∏ j, Fintype.card
        (SixVertexHorizontalTransitionWitness vertical.2.1 j))
    else 0

def sixVertexMarkedSectorRowCyclePairGradeFiberEquiv
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (totalC : Nat) :
    {pair : SixVertexMarkedSectorRowCycle T left ×
        SixVertexMarkedSectorRowCycle T right //
      sixVertexMarkedSectorRowCyclePairTotalC pair = totalC} ≃
      Sigma fun vertical :
          SixVertexVerticalRowsInSector T left ×
            SixVertexVerticalRowsInSector T right =>
        {_witness :
            ((forall j,
                SixVertexHorizontalTransitionWitness vertical.1.1 j) ×
              (forall j,
                SixVertexHorizontalTransitionWitness vertical.2.1 j)) //
          sixVertexVerticalRowsTotalC vertical.1.1 +
            sixVertexVerticalRowsTotalC vertical.2.1 = totalC} :=
  subtypeSigmaBaseEquiv _
    (sixVertexMarkedSectorRowCyclePairEquivVerticalTransitions
      T left right)
    (fun pair => sixVertexMarkedSectorRowCyclePairTotalC pair = totalC)
    (fun vertical => sixVertexVerticalRowsTotalC vertical.1.1 +
      sixVertexVerticalRowsTotalC vertical.2.1 = totalC)
    (fun _ => Iff.rfl)

end
end StatMech.FrontierD
