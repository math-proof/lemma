/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.Language
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Lattice
import Def.v1.Atlas.TheoryOfComputation.code.ContextFree.Part2


namespace ChomskyNormalForm

variable {T : Type*}

/-- A **Pushdown Automaton** (PDA), Sipser, Lecture 4.

Formally, a PDA is a 6-tuple `(Q, Σ, Γ, δ, q₀, F)` where `Σ = α` is the input
alphabet, `Γ = γ` is the stack alphabet, `Q = σ` is the set of states,
`q₀ ∈ Q` is the start state, `F ⊆ Q` is the set of accept states, and
`δ : Q × Σ_ε × Γ_ε → 𝒫(Q × Γ_ε)` is the transition relation (where `_ε` means an
optional symbol, encoded here by `Option`). A move `(q', push) ∈ step q a pop`
means: in state `q`, optionally reading input `a` and optionally popping `pop`
from the stack, go to `q'` and optionally push `push`. -/
structure PDA (α : Type u) (σ : Type v) (γ : Type w) where
  step : σ → Option α → Option γ → Set (σ × Option γ)
  start : σ
  accept : Set σ

end ChomskyNormalForm
