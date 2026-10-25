/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part13
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Decidability
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Set
import Theorem.v1.Atlas.TheoryOfComputation.code.SelfReference


namespace TuringMachine

open TuringMachine

/-- A concrete instance of `TMEncoding` built from the explicit `printTM`
construction. The encoding of a description is taken to be its stored `source`
field, and `printTMDesc w` packages the `printTM w` machine together with
`source := w`, so `q(w) = encode(printTMDesc w) = w` is the identity, which is
clearly computable. -/
noncomputable def concreteTMEncoding (blank : Γ) (inputAlpha : Set Γ)
    (h_blank : blank ∉ inputAlpha) : SelfReference.TMEncoding Γ where
  encode := fun desc => desc.source
  printTMDesc := fun w =>
    { Q := Fin (w.length + 2)
      decEq := inferInstance
      machine := printTM blank inputAlpha h_blank w
      source := w }
  printTMDesc_spec := fun w input => by
    simp only [SelfReference.TMDescription.haltsWithOutput]
    exact printTM_haltsWithOutput blank inputAlpha h_blank w input
  q_computable := by


    show IsComputableFunction (fun w => w)
    refine ⟨Fin 2, inferInstance, {
      blank := blank
      inputAlpha := inputAlpha
      blank_not_in_inputAlpha := h_blank
      δ := fun _ a => (⟨0, by omega⟩, a, Direction.R)
      q₀ := ⟨0, by omega⟩
      qAccept := ⟨0, by omega⟩
      qReject := ⟨1, by omega⟩
      qReject_ne_qAccept := by simp
    }, fun w => ?_⟩


    refine ⟨0, ?_, ?_⟩
    ·
      left
      simp [TM.runOnInput, TM.run, TM.initConfig, TM.isAcceptConfig]
    ·
      simp only [TM.runOnInput, TM.run, TM.initConfig, Config.readTape]
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.length_map, List.length_range] at hi1
        simp only [List.getElem_map, List.getElem_range]
        have h_cond : (0 : ℤ) ≤ ((i : ℕ) : ℤ) ∧ ((i : ℕ) : ℤ) < (w.length : ℤ) := by
          constructor <;> omega
        rw [dif_pos h_cond]
        simp [Int.toNat_natCast]

set_option linter.unusedSectionVars false in

/-- Minimality in the `TMCoding` setting: `M` is minimal if no strictly
shorter-coded index `M'` has the same language. -/
def IsMinimalIndex (C : TMCoding Γ) (M : C.TMIndex) : Prop :=
  ∀ M' : C.TMIndex,
    (C.encode M').length < (C.encode M).length → C.languageOf M' ≠ C.languageOf M

/-- `MIN_TM = {⟨M⟩ | M is a minimal TM}` expressed in the `TMCoding` framework. -/
def MIN_TM_Coding (C : TMCoding Γ) : Set (List Γ) :=
  {s | ∃ M : C.TMIndex, C.encode M = s ∧ IsMinimalIndex C M}

end TuringMachine
