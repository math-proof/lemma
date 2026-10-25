/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneMultiStepBondProgram.Part2
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

noncomputable def encode
    (d : shb_ExplorationDomain V) :
    List (shb_ExplorationSegment V) -> List (Sym2 V)
  | [] => []
  | [s, t] =>
      match edgeOfSegment? d s, edgeOfSegment? d t with
      | some e, some f =>
          if e.1 = f.1 then [s(s.1, s.1)] else [e.1, f.1]
      | _, _ => [s(s.1, s.1)]
  | s :: _ => [s(s.1, s.1)]


def boolSources (st : State V) (omega : Sym2 V -> Bool) : Finset V :=
  sources st.domain.graph (boolCurrent omega)


def terminal (st : State V) (omega : Sym2 V -> Bool) : Prop :=
  match st.accepted with
  | [] => boolSources st omega = ∅
  | [e, f] =>
      if he : e ∈ st.domain.graph.edgeFinset then
        if hf : f ∈ st.domain.graph.edgeFinset then
          let se := canonicalEdgeSegment st.domain.graph ⟨e, he⟩
          let sf := canonicalEdgeSegment st.domain.graph ⟨f, hf⟩
          e ≠ f ∧ se ∈ st.domain.active ∧ sf ∈ st.domain.active ∧
            boolSources st omega = pairSourceClass se sf ∧
            boolSources st omega ≠ ∅
        else False
      else False
  | _ => False


noncomputable def program : BondwiseSegmentProgram V where
  State := State V
  scan := scan
  initial := fun d => ⟨d, []⟩
  encode := encode
  bit := oddBit
  terminal := terminal


def twoUnitFlux (G : SimpleGraph V) (e f : G.edgeFinset) :
    G.edgeFinset -> Nat := fun g => unitFlux G e g + unitFlux G f g

end BackboneMultiStepBondProgram
end
end StatMech.Sharpness
