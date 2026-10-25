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
import Structure.v1.Atlas.TheoryOfComputation.code.SelfReference.Part4


namespace TuringMachine

open TuringMachine

/-- `PrintsAndHalts M w` says: started on the empty tape, `M` reaches an accept
configuration after some `n` steps, with cells `0, …, |w|-1` holding the symbols
of `w` and everywhere else the blank symbol. Captures "M halts having printed
exactly `w`". -/
def PrintsAndHalts {Q : Type} [DecidableEq Q] (M : TM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ,
    M.isAcceptConfig (M.runOnInput [] n) ∧
    (∀ (j : ℕ) (hj : j < w.length),
      (M.runOnInput [] n).tape (j : ℤ) = w[j]'hj) ∧
    (∀ i : ℤ, (i < 0 ∨ (w.length : ℤ) ≤ i) →
      (M.runOnInput [] n).tape i = M.blank)

/-- Same as `PrintsAndHalts` but starting from an arbitrary `input` instead of
the blank tape: after some `n` steps `M` accepts and the first `|w|` tape cells
contain `w`. -/
def PrintsAndHaltsOnInput {Q : Type} [DecidableEq Q] (M : TM Q Γ)
    (input w : List Γ) : Prop :=
  ∃ n : ℕ,
    M.isAcceptConfig (M.runOnInput input n) ∧
    (∀ (j : ℕ) (hj : j < w.length),
      (M.runOnInput input n).tape (j : ℤ) = w[j]'hj)

/-- The concrete *printer-machine* `P_w` for a string `w`: a TM with `|w| + 2`
states (one per character, plus an accept and a reject state) that on any input
writes `w[0], w[1], …, w[|w|-1]` left-to-right and accepts. This is the explicit
construction underlying the computable function `q(w) = ⟨P_w⟩`. -/
noncomputable def printTM (blank : Γ) (inputAlpha : Set Γ) (h_blank : blank ∉ inputAlpha)
    (w : List Γ) : TM (Fin (w.length + 2)) Γ where
  blank := blank
  inputAlpha := inputAlpha
  blank_not_in_inputAlpha := h_blank
  δ := fun q _ =>
    if hq : q.val < w.length then
      (⟨q.val + 1, by omega⟩, w[q.val]'hq, Direction.R)
    else (q, blank, Direction.R)
  q₀ := ⟨0, by omega⟩
  qAccept := ⟨w.length, by omega⟩
  qReject := ⟨w.length + 1, by omega⟩
  qReject_ne_qAccept := by simp

end TuringMachine
