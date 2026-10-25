/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part3
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

noncomputable def encode
    (d : shb_ExplorationDomain V) :
    List (shb_ExplorationSegment V) -> List (Sym2 V)
  | [] => []
  | [s] =>
      match edgeOfSegment? d s with
      | some e => [e.1]
      | none => [s(s.1, s.1)]
  | s :: _ :: _ => [s(s.1, s.1)]


noncomputable def scan :
    shb_DynamicEdgeExploration (State V) (Sym2 V) where
  edgeOrder := fun st =>
    match st.accepted with
    | none => st.domain.graph.edgeFinset.1.toList
    | some _ => []
  edgeOrder_nodup := by
    intro st
    cases st.accepted
    · exact Finset.nodup_toList _
    · simp
  advance := fun st e => ⟨st.domain, some e⟩


def boolSources (st : State V) (omega : Sym2 V -> Bool) : Finset V :=
  sources st.domain.graph (boolCurrent omega)


def terminal (st : State V) (omega : Sym2 V -> Bool) : Prop :=
  match st.accepted with
  | none => boolSources st omega = ∅
  | some e =>
      if he : e ∈ st.domain.graph.edgeFinset then
        canonicalEdgeSegment st.domain.graph ⟨e, he⟩ ∈ st.domain.active /\
          boolSources st omega =
            {(canonicalEdgeSegment st.domain.graph ⟨e, he⟩).1,
              (canonicalEdgeSegment st.domain.graph ⟨e, he⟩).2.1}
      else False


noncomputable def program : BondwiseSegmentProgram V where
  State := State V
  scan := scan
  initial := fun d => ⟨d, none⟩
  encode := encode
  bit := oddBit
  terminal := terminal

end BackboneConcreteBondProgram
end
end StatMech.Sharpness
