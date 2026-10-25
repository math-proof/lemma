/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.RelClasses
import Structure.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4


namespace TuringMachine

open Direction

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- The initial configuration of an enumerator: start state, head at `0`, and
an all-blank tape. -/
def TuringEnumerator.initConfig (E : TuringEnumerator Q Γ) : Config Q Γ where
  state := E.toTM.q₀
  headPos := 0
  tape := fun _ => E.toTM.blank

/-- The configuration of the enumerator after `n` steps. -/
def TuringEnumerator.run (E : TuringEnumerator Q Γ) (n : ℕ) : Config Q Γ :=
  E.toTM.run E.initConfig n

/-- The language `L(E)` enumerated by `E`: all strings `w` that appear in the
print set of some run-step configuration. -/
def TuringEnumerator.language (E : TuringEnumerator Q Γ) : Set (List Γ) :=
  {w | ∃ n : ℕ, w ∈ E.prints (E.run n)}

/-- A language `A` is Turing-enumerable if there is a Turing enumerator `E`
with `L(E) = A`. -/
def IsTuringEnumerable (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (E : TuringEnumerator Q Γ), E.language = A

/-- An auxiliary "counting" TM with state set `ℕ`: it starts in state `2`, never
halts (it never reaches the accept state `0` or reject state `1`), and on each
step increments its state by `1`. Used as the driver for enumerators built from
recognizers. -/
noncomputable def countingTM (blank : Γ) (inputAlpha : Set Γ) (h : blank ∉ inputAlpha) :
    TM ℕ Γ where
  blank := blank
  inputAlpha := inputAlpha
  blank_not_in_inputAlpha := h
  δ := fun q γ => (q + 1, γ, Direction.R)
  q₀ := 2
  qAccept := 0
  qReject := 1
  qReject_ne_qAccept := by omega

/-- Converse direction: every Turing-enumerable language is Turing-recognizable.
A recognizer simulates the enumerator and accepts as soon as it prints the
input string. -/
def TM.haltsWithin (M : TM Q Γ) (w : List Γ) (t : ℕ) : Prop :=
  ∃ n : ℕ, n ≤ t ∧ M.isHaltConfig (M.runOnInput w n)

/-- `M` decides `A` in time `f`: `M` decides `A`, and on every input `w` of
length `n` it halts within `f n` steps. -/
def TM.decidesInTime (M : TM Q Γ) (A : Set (List Γ)) (f : ℕ → ℕ) : Prop :=
  M.decides A ∧ ∀ w : List Γ, M.haltsWithin w (f w.length)

/-- `A` is decidable in (big-O) time `f`: some TM `M` decides `A` within
`c · f n` steps on inputs of length `n`, for some positive constant `c`. -/
def IsDecidableInTime (A : Set (List Γ)) (f : ℕ → ℕ) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : TM Q Γ) (c : ℕ),
    0 < c ∧ M.decidesInTime A (fun n => c * f n)

end TuringMachine
