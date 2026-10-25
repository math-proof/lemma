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
import Inductive.v1.Atlas.TheoryOfComputation.code.TuringMachines


namespace TuringMachine

open Direction

/-- A Turing machine, formalizing Sipser's 7-tuple `(Q, Σ, Γ, δ, q₀, q_acc, q_rej)`:
* `Q` is the set of states,
* `Γ` is the tape alphabet containing a distinguished `blank` symbol,
* `inputAlpha ⊆ Γ` is the input alphabet (excluding `blank`),
* `δ : Q × Γ → Q × Γ × {L, R}` is the transition function,
* `q₀`, `qAccept`, `qReject` are the start, accept and reject states (with
  `qReject ≠ qAccept`). -/
structure TM (Q : Type) (Γ : Type) where
  blank : Γ
  inputAlpha : Set Γ
  blank_not_in_inputAlpha : blank ∉ inputAlpha
  δ : Q → Γ → Q × Γ × Direction
  q₀ : Q
  qAccept : Q
  qReject : Q
  qReject_ne_qAccept : qReject ≠ qAccept

end TuringMachine
