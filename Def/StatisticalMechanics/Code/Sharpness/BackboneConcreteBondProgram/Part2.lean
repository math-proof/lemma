/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Structure.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part2
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

noncomputable def canonicalEdgeSegment
    (G : SimpleGraph V)
    (e : G.edgeFinset) : shb_ExplorationSegment V := by
  let a := e.1.out.1
  let b := e.1.out.2
  have hab : s(a, b) = e.1 := e.1.out_eq
  have habne : a ≠ b := by
    intro h
    have hedge : e.1 ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
    apply G.not_isDiag_of_mem_edgeSet hedge
    rw [← hab, Sym2.mk_isDiag_iff]
    exact h
  let w : (⊤ : SimpleGraph V).Walk a b :=
    SimpleGraph.Walk.cons (by simpa using habne) SimpleGraph.Walk.nil
  exact ⟨a, b, ⟨w, by simpa [w] using habne⟩⟩


end BackboneConcreteBondProgram
end
end StatMech.Sharpness
