/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RegularLanguages.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Powerset
open Computability


/-- A finite automaton over alphabet `α` with state space `σ`, defined as a `DFA α σ`.

In Sipser's textbook, a finite automaton is a 5-tuple `(Q, Σ, δ, q₀, F)` where
`Q` is a finite set of states, `Σ` a finite alphabet, `δ : Q × Σ → Q` the
transition function, `q₀` the start state, and `F ⊆ Q` the accept states.
This is exactly the data packaged by Mathlib's `DFA`. -/
abbrev FiniteAutomaton (α : Type*) (σ : Type*) := DFA α σ

