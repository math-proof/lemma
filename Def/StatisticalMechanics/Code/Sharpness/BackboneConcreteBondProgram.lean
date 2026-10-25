/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Structure.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

noncomputable def SelectorRealization.toCompleteSpec
    {P : BondwiseSegmentProgram V}
    {S : shb_PartialCurrentDynamicSelector (V := V)}
    (R : SelectorRealization P S) : CompleteBondwiseSelectorSpec P where
  sourceClass := S.sourceClass
  sourceClass_nil := S.sourceClass_nil
  complete_functional := by
    intro d m word word' hword hword'
    have hfiber := (R.complete_iff_fiber d word m).mp hword
    have hfiber' := (R.complete_iff_fiber d word' m).mp hword'
    unfold shb_PartialCurrentDynamicSelector.Fiber at hfiber hfiber'
    exact Option.some.inj (hfiber.symm.trans hfiber')
  sources_eq_sourceClass_of_complete := by
    intro d m word hword
    exact S.sources_eq_sourceClass_of_select d m word
      ((R.complete_iff_fiber d word m).mp hword)
  complete_nil_iff := by
    intro d m
    exact (R.complete_iff_fiber d [] m).trans
      (S.select?_eq_some_nil_iff d m)
  head_active_of_complete := by
    intro d m s ss hword
    exact S.head_active_of_select d m s ss
      ((R.complete_iff_fiber d (s :: ss) m).mp hword)


def boolCurrent (omega : Sym2 V -> Bool) : Current V :=
  fun e => if omega e then 1 else 0


def oddBit (n : Nat) : Bool := decide (Odd n)

end BackboneConcreteBondProgram
end
end StatMech.Sharpness
