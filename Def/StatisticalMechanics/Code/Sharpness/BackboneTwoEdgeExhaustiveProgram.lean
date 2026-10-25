/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part9
import Instance.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeExhaustiveProgram
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeExhaustiveProgram

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackboneP2CoordinateReindex

open FluxEdgeCopy

def NoFurtherOdd (st : BackboneTwoEdgeBondProgram.State V) (e f : Sym2 V)
    (omega : Sym2 V -> Bool) : Prop :=
  forall g, g ∈ st.domain.graph.edgeFinset -> g ≠ e -> g ≠ f ->
    omega g = false


def terminal (st : BackboneTwoEdgeBondProgram.State V)
    (omega : Sym2 V -> Bool) : Prop :=
  BackboneTwoEdgeBondProgram.terminal st omega /\
    match st.accepted with
    | [e, f] => NoFurtherOdd st e f omega
    | _ => True


noncomputable def program : BondwiseSegmentProgram V where
  State := BackboneTwoEdgeBondProgram.State V
  scan := BackboneTwoEdgeBondProgram.scan
  initial := fun d => ⟨d, []⟩
  encode := BackboneTwoEdgeBondProgram.encode
  bit := oddBit
  terminal := terminal


end BackboneTwoEdgeExhaustiveProgram
end
end StatMech.Sharpness
