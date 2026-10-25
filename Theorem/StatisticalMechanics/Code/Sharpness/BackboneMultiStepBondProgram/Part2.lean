/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneMultiStepBondProgram.Part2
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneMultiStepBondProgram

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneDeterminedCutSwitching

theorem IsDesignatedPair.ne
    {d : shb_ExplorationDomain V} {e f : d.graph.edgeFinset}
    (h : IsDesignatedPair d e f) : e.1 ≠ f.1 := by
  rcases h with ⟨tail, horder⟩
  have hnodup := Finset.nodup_toList d.graph.edgeFinset
  change d.graph.edgeFinset.1.toList.Nodup at hnodup
  rw [horder] at hnodup
  intro hef
  exact (List.nodup_cons.mp hnodup).1 (by simp [hef])

theorem scan_edgeOrder_initial_of_designated
    {d : shb_ExplorationDomain V} {e f : d.graph.edgeFinset}
    (h : IsDesignatedPair d e f) :
    scan.edgeOrder ⟨d, []⟩ = [e.1] := by
  rcases h with ⟨tail, horder⟩
  simp [scan, horder]

theorem scan_edgeOrder_second_of_designated
    {d : shb_ExplorationDomain V} {e f : d.graph.edgeFinset}
    (h : IsDesignatedPair d e f) :
    scan.edgeOrder (scan.advance ⟨d, []⟩ e.1) = [f.1] := by
  rcases h with ⟨tail, horder⟩
  simp [scan, horder]


end BackboneMultiStepBondProgram
end
end StatMech.Sharpness
