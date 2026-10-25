/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NFA.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.EpsilonNFA
open Computability Set


namespace Sipser

/-- **Nondeterministic Empty.Finite Automaton (Sipser-style).**

An NFA is a 5-tuple `(Q, Σ, δ, q₀, F)` where `Q` is a finite set of states,
`Σ` an alphabet, `q₀ ∈ Q` the start state, `F ⊆ Q` the accept states, and
`δ : Q × Σ_ε → 𝒫(Q)` the transition function (where `Σ_ε = Σ ∪ {ε}`).

Here `δ q (some a)` gives the transitions on input symbol `a`, while
`δ q none` gives the ε-transitions. Successor sets are represented as
`Finset Q`. The alphabet `Σ` and the implicit `Q` are tracked by the type
parameters. -/
structure NFA (Q : Type*) (σ : Type*) [DecidableEq Q] where
  δ : Q → Option σ → Finset Q
  q₀ : Q
  accept : Finset Q

end Sipser
