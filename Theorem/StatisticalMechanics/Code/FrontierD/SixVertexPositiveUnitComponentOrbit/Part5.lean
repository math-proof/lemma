/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part5
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitBase

variable {T : EvenTorus} {middle : Fin (T.width + 1)} {k : Nat}


theorem sourceComponentSeed_edge
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (component : SixVertexDisagreementComponent base.first base.second) :
    sixVertexDegreeTwoOrientedComponentEdge
        (base.source_degreeTwo positive hmiddle_pos hmiddle_lt)
        (base.sourceComponentSeed positive hmiddle_pos hmiddle_lt component) =
      base.componentRepresentativeEdge component := by
  exact congrArg Subtype.val
    ((sixVertexOrientedDisagreementDartEquivEdge
      (base.source positive hmiddle_pos hmiddle_lt).1.2.1
      (base.source positive hmiddle_pos hmiddle_lt).2.2.1
      (base.source_degreeTwo positive hmiddle_pos hmiddle_lt)).apply_symm_apply
        ⟨base.componentRepresentativeEdge component, by
          change sixVertexTorusEdgeDisagrees
            (sixVertexTorusSwitchFirst (base.mask positive)
              base.first base.second)
            (sixVertexTorusSwitchSecond (base.mask positive)
              base.first base.second)
            (base.componentRepresentativeEdge component)
          rw [sixVertexTorusEdgeDisagrees_pairSwitch_iff]
          exact base.componentRepresentativeEdge_disagrees component⟩)


theorem sourceComponentSeed_strandMask
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (component : SixVertexDisagreementComponent base.first base.second) :
    (sixVertexDegreeTwoStrandDirectedSimpleCycle
      (base.source positive hmiddle_pos hmiddle_lt).1.2.1
      (base.source positive hmiddle_pos hmiddle_lt).2.2.1
      (base.source_degreeTwo positive hmiddle_pos hmiddle_lt)
      (base.sourceComponentSeed positive hmiddle_pos hmiddle_lt component)).mask =
    sixVertexDisagreementComponentSetMask base.first base.second
      {component} := by
  apply sixVertexDegreeTwoStrand_mask_eq_reference_component
    (base.source positive hmiddle_pos hmiddle_lt).1.2.1
    (base.source positive hmiddle_pos hmiddle_lt).2.2.1
    (base.source_degreeTwo positive hmiddle_pos hmiddle_lt)
    (sixVertexTorusDisagreementGraph_pairSwitch
      (base.mask positive) base.first base.second)
    component
  rw [base.sourceComponentSeed_edge positive hmiddle_pos hmiddle_lt component]
  exact base.componentRepresentativeEdge_component component


theorem physicalRelated_of_related
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (target : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) k)
    (hrelated : booleanMiddleLayerDownRelation source target) :
    SixVertexDegreeTwoUnitStrandPhysicalRelated
      (base.sourceEmbedding hmiddle_pos hmiddle_lt source)
      (base.targetEmbedding target) := by
  let component := booleanMiddleLayerAddedElement target source
  let sourcePhysical := base.source source hmiddle_pos hmiddle_lt
  let targetPhysical := base.target target
  let hdegree := base.source_degreeTwo source hmiddle_pos hmiddle_lt
  let seed := base.sourceComponentSeed source hmiddle_pos hmiddle_lt component
  let componentMask := sixVertexDisagreementComponentSetMask
    base.first base.second {component}
  let strandMask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    sourcePhysical.1.2.1 sourcePhysical.2.2.1 hdegree seed).mask
  have hstrandMask : strandMask = componentMask := by
    exact base.sourceComponentSeed_strandMask source hmiddle_pos hmiddle_lt
      component
  have htargetMask : base.mask target =
      sixVertexTorusMaskXor (base.mask source) componentMask := by
    exact base.target_mask_eq_xor_of_related source target hrelated
  have hsupport : forall edge,
      sixVertexTorusMaskSelects componentMask edge = true →
      sixVertexTorusEdgeDisagrees sourcePhysical.1.1
        sourcePhysical.2.1 edge := by
    intro edge hselected
    change sixVertexTorusEdgeDisagrees
      (sixVertexTorusSwitchFirst (base.mask source)
        base.first base.second)
      (sixVertexTorusSwitchSecond (base.mask source)
        base.first base.second) edge
    rw [sixVertexTorusEdgeDisagrees_pairSwitch_iff]
    exact sixVertexDisagreementComponentSetMask_selects_only_disagreement
      base.first base.second {component} edge hselected
  have hfirstArrows : sixVertexTorusFlip strandMask sourcePhysical.1.1 =
      targetPhysical.1.1 := by
    rw [hstrandMask]
    rw [← sixVertexTorusSwitchFirst_eq_flip_of_disagrees hsupport]
    change sixVertexTorusSwitchFirst componentMask
        (sixVertexTorusSwitchFirst (base.mask source)
          base.first base.second)
        (sixVertexTorusSwitchSecond (base.mask source)
          base.first base.second) =
      sixVertexTorusSwitchFirst (base.mask target) base.first base.second
    rw [sixVertexTorusSwitchFirst_pairSwitch, htargetMask]
  have hsecondArrows : sixVertexTorusFlip strandMask sourcePhysical.2.1 =
      targetPhysical.2.1 := by
    rw [hstrandMask]
    rw [← sixVertexTorusSwitchSecond_eq_flip_of_disagrees hsupport]
    change sixVertexTorusSwitchSecond componentMask
        (sixVertexTorusSwitchFirst (base.mask source)
          base.first base.second)
        (sixVertexTorusSwitchSecond (base.mask source)
          base.first base.second) =
      sixVertexTorusSwitchSecond (base.mask target) base.first base.second
    rw [sixVertexTorusSwitchSecond_pairSwitch, htargetMask]
  have hdelta :=
    sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta_eq_wordSum
      sourcePhysical.1.2.1 sourcePhysical.2.2.1 hdegree seed
  have hdeltaOne : sixVertexTorusFlipSeamDelta strandMask
      sourcePhysical.1.1 = 1 := by
    have hcount := sixVertexTorusFlip_upCount strandMask sourcePhysical.1.1
    rw [hfirstArrows, targetPhysical.1.2.2,
      sourcePhysical.1.2.2] at hcount
    simp only [Fin.val_mk] at hcount
    have hmpos := hmiddle_pos
    omega
  have hunit : (sixVertexDegreeTwoStrandSeamWord
      sourcePhysical.1.2.1 sourcePhysical.2.2.1 hdegree seed).sum = 1 :=
    hdelta.symm.trans hdeltaOne
  refine ⟨hdegree, seed, hunit, ?_⟩
  apply Prod.ext <;> apply Subtype.ext
  · exact hfirstArrows.symm
  · exact hsecondArrows.symm


theorem related_of_physicalRelated
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (target : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) k)
    (hphysical : SixVertexDegreeTwoUnitStrandPhysicalRelated
      (base.sourceEmbedding hmiddle_pos hmiddle_lt source)
      (base.targetEmbedding target)) :
    booleanMiddleLayerDownRelation source target := by
  obtain ⟨hdegree, seed, hunit, htarget⟩ := hphysical
  let sourcePhysical := base.source source hmiddle_pos hmiddle_lt
  let targetPhysical := base.target target
  let edge := sixVertexDegreeTwoOrientedComponentEdge hdegree seed
  have hedgeSource : sixVertexTorusEdgeDisagrees
      sourcePhysical.1.1 sourcePhysical.2.1 edge := by
    exact (sixVertexDegreeTwoLocalMate hdegree seed.1).2
  have hedgeBase : sixVertexTorusEdgeDisagrees base.first base.second edge := by
    rw [← sixVertexTorusEdgeDisagrees_pairSwitch_iff
      (base.mask source) base.first base.second edge]
    exact hedgeSource
  let component : SixVertexDisagreementComponent base.first base.second :=
    ⟨(sixVertexTorusDisagreementGraph base.first base.second).connectedComponentMk
        edge,
      ⟨edge, hedgeBase, rfl⟩⟩
  let componentMask := sixVertexDisagreementComponentSetMask
    base.first base.second {component}
  let strandMask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    sourcePhysical.1.2.1 sourcePhysical.2.2.1 hdegree seed).mask
  have hstrandMask : strandMask = componentMask := by
    apply sixVertexDegreeTwoStrand_mask_eq_reference_component
      sourcePhysical.1.2.1 sourcePhysical.2.2.1 hdegree
      (sixVertexTorusDisagreementGraph_pairSwitch
        (base.mask source) base.first base.second)
      component seed
    rfl
  have hsupport : forall selectedEdge,
      sixVertexTorusMaskSelects componentMask selectedEdge = true →
      sixVertexTorusEdgeDisagrees sourcePhysical.1.1
        sourcePhysical.2.1 selectedEdge := by
    intro selectedEdge hselected
    change sixVertexTorusEdgeDisagrees
      (sixVertexTorusSwitchFirst (base.mask source)
        base.first base.second)
      (sixVertexTorusSwitchSecond (base.mask source)
        base.first base.second) selectedEdge
    rw [sixVertexTorusEdgeDisagrees_pairSwitch_iff]
    exact sixVertexDisagreementComponentSetMask_selects_only_disagreement
      base.first base.second {component} selectedEdge hselected
  have htargetFirst : targetPhysical.1.1 =
      sixVertexTorusFlip strandMask sourcePhysical.1.1 := by
    have harrows := congrArg (fun physical => physical.1.1) htarget
    change targetPhysical.1.1 =
      sixVertexTorusFlip strandMask sourcePhysical.1.1 at harrows
    exact harrows
  have hfirstSwitch :
      sixVertexTorusSwitchFirst (base.mask target)
          base.first base.second =
        sixVertexTorusSwitchFirst
          (sixVertexTorusMaskXor (base.mask source) componentMask)
          base.first base.second := by
    calc
      sixVertexTorusSwitchFirst (base.mask target)
          base.first base.second = targetPhysical.1.1 := rfl
      _ = sixVertexTorusFlip strandMask sourcePhysical.1.1 := htargetFirst
      _ = sixVertexTorusFlip componentMask sourcePhysical.1.1 := by
        rw [hstrandMask]
      _ = sixVertexTorusSwitchFirst componentMask
          sourcePhysical.1.1 sourcePhysical.2.1 :=
        (sixVertexTorusSwitchFirst_eq_flip_of_disagrees hsupport).symm
      _ = sixVertexTorusSwitchFirst
          (sixVertexTorusMaskXor (base.mask source) componentMask)
          base.first base.second := by
        exact sixVertexTorusSwitchFirst_pairSwitch
          (base.mask source) componentMask base.first base.second
  let toggled := base.negativeComponents source ∆ {component}
  have htoggledMask :
      sixVertexDisagreementComponentSetMask base.first base.second toggled =
        sixVertexTorusMaskXor (base.mask source) componentMask := by
    exact sixVertexDisagreementComponentSetMask_symmDiff
      base.first base.second (base.negativeComponents source) {component}
  have hmaskSet : base.mask target =
      sixVertexDisagreementComponentSetMask base.first base.second toggled := by
    apply sixVertexTorusSwitchFirst_injective_on_fullMasks
      (base.mask_full target)
      (sixVertexDisagreementComponentSetMask_full
        base.first base.second toggled)
    rw [htoggledMask]
    exact hfirstSwitch
  apply base.related_of_target_mask_eq_xor source target component
  exact hmaskSet.trans htoggledMask


theorem physicalRelated_iff
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (target : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) k) :
    SixVertexDegreeTwoUnitStrandPhysicalRelated
        (base.sourceEmbedding hmiddle_pos hmiddle_lt source)
        (base.targetEmbedding target) ↔
      booleanMiddleLayerDownRelation source target :=
  ⟨base.related_of_physicalRelated hmiddle_pos hmiddle_lt source target,
    base.physicalRelated_of_related hmiddle_pos hmiddle_lt source target⟩


end SixVertexPositiveUnitComponentOrbitBase
end
end StatMech.FrontierD
