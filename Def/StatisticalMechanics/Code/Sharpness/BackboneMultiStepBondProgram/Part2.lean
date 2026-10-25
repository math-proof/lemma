/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Structure.StatisticalMechanics.Code.Sharpness.BackboneMultiStepBondProgram
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

noncomputable def scan :
    shb_DynamicEdgeExploration (State V) (Sym2 V) where
  edgeOrder := fun st =>
    match st.accepted with
    | [] => st.domain.graph.edgeFinset.1.toList.take 1
    | [e] => (st.domain.graph.edgeFinset.1.toList.erase e).take 1
    | _ => []
  edgeOrder_nodup := by
    intro st
    rcases st with ⟨d, accepted⟩
    cases accepted with
    | nil => exact (Finset.nodup_toList d.graph.edgeFinset).take
    | cons e rest =>
        cases rest with
        | nil =>
            exact ((Finset.nodup_toList d.graph.edgeFinset).erase e).take
        | cons f rest => simp
  advance := fun st e =>
    match st.accepted with
    | [] => ⟨st.domain, [e]⟩
    | [first] => ⟨st.domain, [first, e]⟩
    | _ => st


def IsDesignatedPair (d : shb_ExplorationDomain V)
    (e f : d.graph.edgeFinset) : Prop :=
  ∃ tail, d.graph.edgeFinset.1.toList = e.1 :: f.1 :: tail

end BackboneMultiStepBondProgram
end
end StatMech.Sharpness
