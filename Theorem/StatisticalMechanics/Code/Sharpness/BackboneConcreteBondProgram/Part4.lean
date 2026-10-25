/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Def.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part4
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

@[simp] theorem program_complete_nil_iff
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    program.CompleteEvent d [] m <->
      sources d.graph (ofEdgeFun d.graph m) = ∅ := by
  change (True /\ sources d.graph
    (boolCurrent (fluxBitConfig d.graph oddBit m)) = ∅) <-> _
  rw [sources_boolCurrent_oddBit]
  simp


theorem scan_firstAdmissible_ne_diagonal
    (d : shb_ExplorationDomain V) (omega : Sym2 V -> Bool) (x : V) :
    scan.firstAdmissible (fun _ e => omega e) ⟨d, none⟩ ≠ some s(x, x) := by
  intro h
  have hmem := scan.firstAdmissible_mem (fun _ e => omega e)
    ⟨d, none⟩ s(x, x) h
  have hedge : s(x, x) ∈ d.graph.edgeFinset := by
    simpa [scan] using hmem
  have hadj : d.graph.Adj x x := by
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
  exact d.graph.loopless.irrefl x hadj


theorem find?_eq_some_of_unique_true
    {A : Type*} [DecidableEq A] (xs : List A) (a : A) (p : A -> Bool)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hp : ∀ x, p x = true <-> x = a) :
    xs.find? p = some a := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        simp [List.find?, (hp a).mpr rfl]
      · have ha' : a ∈ xs := by
          rcases List.mem_cons.mp ha with hax | ha'
          · exact (hxa hax.symm).elim
          · exact ha'
        cases hpx : p x with
        | false => simpa [List.find?, hpx] using ih hnodup.2 ha'
        | true => exact (hxa ((hp x).mp hpx)).elim


end BackboneConcreteBondProgram
end
end StatMech.Sharpness
