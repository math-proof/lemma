/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part3
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitBase

variable {T : EvenTorus} {middle : Fin (T.width + 1)} {k : Nat}


theorem source_degreeTwo
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    SixVertexLocallyDegreeTwo
      (base.source positive hmiddle_pos hmiddle_lt).1.1
      (base.source positive hmiddle_pos hmiddle_lt).2.1 := by
  change SixVertexLocallyDegreeTwo
    (sixVertexTorusSwitchFirst (base.mask positive)
      base.first base.second)
    (sixVertexTorusSwitchSecond (base.mask positive)
      base.first base.second)
  exact base.degreeTwo.pairSwitch


theorem target_mask_eq_xor_of_related
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (source : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (target : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) k)
    (hrelated : booleanMiddleLayerDownRelation source target) :
    base.mask target = sixVertexTorusMaskXor (base.mask source)
      (sixVertexDisagreementComponentSetMask base.first base.second
        {booleanMiddleLayerAddedElement target source}) := by
  let component := booleanMiddleLayerAddedElement target source
  have hsource := booleanMiddleLayer_source_eq_insert_addedElement
    target source hrelated
  have hnegative : base.negativeComponents target =
      base.negativeComponents source ∆ {component} := by
    ext other
    dsimp [component]
    simp only [negativeComponents, Finset.mem_compl,
      Finset.mem_symmDiff, Finset.mem_singleton]
    rw [hsource]
    by_cases hother : other = booleanMiddleLayerAddedElement target source
    · subst other
      simp [booleanMiddleLayerAddedElement_not_mem_target]
    · simp [hother]
  rw [mask, mask, hnegative,
    sixVertexDisagreementComponentSetMask_symmDiff]


theorem related_of_target_mask_eq_xor
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (source : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (target : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) k)
    (component : SixVertexDisagreementComponent base.first base.second)
    (hmasks : base.mask target = sixVertexTorusMaskXor (base.mask source)
      (sixVertexDisagreementComponentSetMask base.first base.second
        {component})) :
    booleanMiddleLayerDownRelation source target := by
  have hsets : base.negativeComponents target =
      base.negativeComponents source ∆ {component} := by
    apply sixVertexDisagreementComponentSetMask_injective
      base.first base.second
    rw [sixVertexDisagreementComponentSetMask_symmDiff]
    exact hmasks
  have hcomponent : component ∉ base.negativeComponents source := by
    intro hmem
    have herase : base.negativeComponents source ∆ {component} =
        (base.negativeComponents source).erase component := by
      ext other
      by_cases hother : other = component
      · subst other
        simp [Finset.mem_symmDiff, hmem]
      · simp [Finset.mem_symmDiff, hother]
    have hcard := congrArg Finset.card hsets
    rw [herase, Finset.card_erase_of_mem hmem,
      base.negativeComponents_card target,
      base.negativeComponents_card source] at hcard
    have hkpos := base.k_pos
    omega
  intro other htarget
  by_contra hsource
  have hnegativeSource : other ∈ base.negativeComponents source := by
    simp [negativeComponents, hsource]
  have hne : other ≠ component := by
    intro heq
    apply hcomponent
    simpa [heq] using hnegativeSource
  have hsymm : other ∈ base.negativeComponents source ∆ {component} :=
    (Finset.mem_symmDiff).2 (Or.inl ⟨hnegativeSource, by simp [hne]⟩)
  have hnegativeTarget : other ∈ base.negativeComponents target := by
    rw [hsets]
    exact hsymm
  simp [negativeComponents, htarget] at hnegativeTarget


end SixVertexPositiveUnitComponentOrbitBase
end
end StatMech.FrontierD
