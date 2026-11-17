/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.Language
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Set.Finite.Lattice
public import Abbrev.v1.Atlas.TheoryOfComputation.code.ContextFree

@[expose] public section

namespace ChomskyNormalForm

variable {T : Type*}

/-- A rule `r : A → α` is in *Chomsky Normal Form* if its right-hand side has one
of the following forms:
* `A → BC` where `B, C` are nonterminals distinct from the start variable, or
* `A → a` where `a` is a single terminal symbol, or
* `S → ε` where `S` is the start variable (the only allowed ε-production). -/
def IsCNFRule {N : Type*} (r : ContextFreeRule T N) (startVar : N) : Prop :=
  (∃ B C : N, B ≠ startVar ∧ C ≠ startVar ∧
    r.output = [Symbol.nonterminal B, Symbol.nonterminal C]) ∨
  (∃ a : T, r.output = [Symbol.terminal a]) ∨
  (r.input = startVar ∧ r.output = [])

/-- A grammar `g` is in Chomsky Normal Form iff every one of its rules is. -/
def IsCNF (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, IsCNFRule r g.initial

end ChomskyNormalForm
