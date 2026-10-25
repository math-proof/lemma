/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationCutAdmissible.Part3
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem shb_generatedExplorationFiberMass_cutResummation
    (beta : Real) (J : Sym2 V -> Real) :
    shb_LocalSelectorFiberCutResummation beta J
      (shb_generatedExplorationFiberMass beta J : shb_ExplorationFiberMass V) := by
  refine ⟨fun d => rfl, ?_, ?_⟩
  · intro d s ss hs
    rw [shb_generatedExplorationFiberMass, if_pos hs]
    have hZ : currentSum
        (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ ≠ 0 :=
      ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos
        (shb_BackboneExplorationDomain.advance d s).graph beta J)
    field_simp [hZ]
  · intro d s ss hs
    rw [shb_generatedExplorationFiberMass, if_neg hs]


theorem shb_LocalSelectorFiberCutResummation_unique
    (beta : Real) (J : Sym2 V -> Real)
    (fiberMass : shb_ExplorationFiberMass V)
    (hcut : shb_LocalSelectorFiberCutResummation beta J fiberMass) :
    fiberMass = shb_generatedExplorationFiberMass beta J := by
  funext d word
  induction word generalizing d with
  | nil =>
      rw [shb_generatedExplorationFiberMass]
      exact hcut.1 d
  | cons s ss ih =>
      by_cases hs : s ∈ d.active
      · let d' := shb_BackboneExplorationDomain.advance d s
        have hZ : currentSum d'.graph beta J ∅ ≠ 0 :=
          ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos d'.graph beta J)
        rw [shb_generatedExplorationFiberMass, if_pos hs]
        apply (eq_div_iff hZ).2
        rw [hcut.2.1 d s ss hs, ih d']
      · rw [hcut.2.2 d s ss hs, shb_generatedExplorationFiberMass, if_neg hs]


theorem shb_LocalSelectorFiberCutResummation_iff_eq_generated
    (beta : Real) (J : Sym2 V -> Real)
    (fiberMass : shb_ExplorationFiberMass V) :
    shb_LocalSelectorFiberCutResummation beta J fiberMass <->
      fiberMass = shb_generatedExplorationFiberMass beta J := by
  constructor
  · exact shb_LocalSelectorFiberCutResummation_unique beta J fiberMass
  · rintro rfl
    exact shb_generatedExplorationFiberMass_cutResummation beta J

end
end StatMech.Sharpness
