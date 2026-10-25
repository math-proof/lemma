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
import Inductive.v1.Atlas.TheoryOfComputation.code.ContextFree.Part2


namespace ChomskyNormalForm

variable {T : Type*}

namespace PDA

variable {α : Type u} {σ : Type v} {γ : Type w}

variable (M : PDA α σ γ)

/-- The reflexive transitive closure of `Step`: `c ⊢* c'` means `c` can reach
`c'` in zero or more PDA moves. -/
def Reaches : Config (α := α) (σ := σ) (γ := γ) →
    Config (α := α) (σ := σ) (γ := γ) → Prop :=
  Relation.ReflTransGen M.Step

/-- `M` accepts the input string `w` if, starting from `(q₀, w, ε)`, some
sequence of moves consumes all of `w` and ends in an accept state (the final
stack contents are arbitrary). -/
def Accepts (w : List α) : Prop :=
  ∃ q ∈ M.accept, ∃ stack : List γ, M.Reaches (M.start, w, []) (q, [], stack)

/-- The language recognised by the PDA: `L(M) = { w ∈ Σ* | M accepts w }`. -/
def language : Language α :=
  { w | M.Accepts w }

end PDA

/-- `listPow l n` is the list `l` repeated `n` times (i.e. `l^n` in the free
monoid of lists). Used to express the pumped strings `v^i` and `y^i` in the CFL
pumping lemma. -/
def listPow (l : List α) : Nat → List α
  | 0 => []
  | n + 1 => l ++ listPow l n

end ChomskyNormalForm
