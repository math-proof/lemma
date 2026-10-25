/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateToggleObstruction
import Structure.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelector.Part2
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneP2CoordinateToggleObstruction

open FluxEdgeCopy

variable {D : Type*}


noncomputable def CompleteBondwiseSelectorSpec.select?
    {P : BondwiseSegmentProgram V} (_R : CompleteBondwiseSelectorSpec P)
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    Option (List (shb_ExplorationSegment V)) := by
  classical
  exact if h : ∃ word, P.CompleteEvent d word m then some (Classical.choose h)
    else none


noncomputable def CompleteBondwiseSelectorSpec.toPartialSelector
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P) :
    shb_PartialCurrentDynamicSelector (V := V) where
  sourceClass := R.sourceClass
  select? := R.select?
  sourceClass_nil := R.sourceClass_nil
  sources_eq_sourceClass_of_select := by
    intro d m word hword
    unfold CompleteBondwiseSelectorSpec.select? at hword
    split at hword
    · rename_i hex
      have hchosen : Classical.choose hex = word := Option.some.inj hword
      exact R.sources_eq_sourceClass_of_complete d m word
        (hchosen ▸ Classical.choose_spec hex)
    · simp at hword
  select?_eq_some_nil_iff := by
    intro d m
    constructor
    · intro hselect
      unfold CompleteBondwiseSelectorSpec.select? at hselect
      split at hselect
      · rename_i hex
        have hchosen : Classical.choose hex = [] := Option.some.inj hselect
        exact (R.complete_nil_iff d m).mp
          (hchosen ▸ Classical.choose_spec hex)
      · simp at hselect
    · intro hsrc
      have hnil : P.CompleteEvent d [] m := (R.complete_nil_iff d m).mpr hsrc
      let hex : ∃ word, P.CompleteEvent d word m := ⟨[], hnil⟩
      unfold CompleteBondwiseSelectorSpec.select?
      rw [dif_pos hex]
      apply congrArg some
      exact R.complete_functional d m (Classical.choose hex) []
        (Classical.choose_spec hex) hnil
  head_active_of_select := by
    intro d m s ss hselect
    unfold CompleteBondwiseSelectorSpec.select? at hselect
    split at hselect
    · rename_i hex
      have hchosen : Classical.choose hex = s :: ss := Option.some.inj hselect
      exact R.head_active_of_complete d m s ss
        (hchosen ▸ Classical.choose_spec hex)
    · simp at hselect


end BackboneConcreteSelector
end
end StatMech.Sharpness
