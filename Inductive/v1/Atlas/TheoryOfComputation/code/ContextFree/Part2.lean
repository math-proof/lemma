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
import Abbrev.v1.Atlas.TheoryOfComputation.code.ContextFree.Part2


namespace ChomskyNormalForm

variable {T : Type*}

namespace PDA

variable {α : Type u} {σ : Type v} {γ : Type w}

variable (M : PDA α σ γ)

/-- One step of the PDA: read (optionally) an input symbol `a`, pop (optionally)
`pop` from the top of the stack, transition to `q'`, and push (optionally) `push`
on top of the stack. -/
inductive Step : Config (α := α) (σ := σ) (γ := γ) →
    Config (α := α) (σ := σ) (γ := γ) → Prop where
  | mk (q q' : σ) (a : Option α) (pop : Option γ) (push : Option γ)
      (input : List α) (stack : List γ) :
    (q', push) ∈ M.step q a pop →
    Step
      (q, a.toList ++ input, pop.toList ++ stack)
      (q', input, push.toList ++ stack)

end PDA
end ChomskyNormalForm
