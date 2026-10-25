/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Structure.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeBondProgram

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneDeterminedCutSwitching

noncomputable def scan :
    shb_DynamicEdgeExploration (State V) (Sym2 V) where
  edgeOrder := fun st =>
    match st.accepted with
    | [] => st.domain.graph.edgeFinset.1.toList
    | [first] => (st.domain.graph.edgeFinset.erase first).1.toList
    | _ => []
  edgeOrder_nodup := by
    intro st
    cases st.accepted with
    | nil => exact Finset.nodup_toList _
    | cons first rest =>
        cases rest with
        | nil => exact Finset.nodup_toList _
        | cons second tail => simp
  advance := fun st e => ⟨st.domain, st.accepted ++ [e]⟩


noncomputable def encode
    (d : shb_ExplorationDomain V) :
    List (shb_ExplorationSegment V) -> List (Sym2 V)
  | [] => []
  | [s] =>
      match edgeOfSegment? d s with
      | some e => [e.1]
      | none => [s(s.1, s.1)]
  | [s, t] =>
      match edgeOfSegment? d s, edgeOfSegment? d t with
      | some e, some f => [e.1, f.1]
      | _, _ => [s(s.1, s.1)]
  | s :: _ :: _ :: _ => [s(s.1, s.1)]


def FormsTwoEdgePath
    (s t : shb_ExplorationSegment V) : Prop :=
  s.2.1 = t.1 /\ s.1 ≠ t.2.1


def boolSources (st : State V) (omega : Sym2 V -> Bool) : Finset V :=
  sources st.domain.graph
    (BackboneConcreteBondProgram.boolCurrent omega)


def terminal (st : State V) (omega : Sym2 V -> Bool) : Prop :=
  match st.accepted with
  | [] => boolSources st omega = ∅
  | [e] =>
      if he : e ∈ st.domain.graph.edgeFinset then
        let s := canonicalEdgeSegment st.domain.graph ⟨e, he⟩
        s ∈ st.domain.active /\
          boolSources st omega = {s.1, s.2.1} /\
          scan.firstAdmissible (fun _ b => omega b) st = none
      else False
  | [e, f] =>
      if he : e ∈ st.domain.graph.edgeFinset then
        if hf : f ∈ st.domain.graph.edgeFinset then
          let s := canonicalEdgeSegment st.domain.graph ⟨e, he⟩
          let t := canonicalEdgeSegment st.domain.graph ⟨f, hf⟩
          e ≠ f /\ s ∈ st.domain.active /\ t ∈ st.domain.active /\
            FormsTwoEdgePath s t /\
            boolSources st omega = {s.1, s.2.1} ∆ {t.1, t.2.1}
        else False
      else False
  | _ => False


noncomputable def program : BondwiseSegmentProgram V where
  State := State V
  scan := scan
  initial := fun d => ⟨d, []⟩
  encode := encode
  bit := BackboneConcreteBondProgram.oddBit
  terminal := terminal

end BackboneTwoEdgeBondProgram
end
end StatMech.Sharpness
