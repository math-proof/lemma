/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
public import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part13
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Decidability
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Set
public import Structure.v1.Atlas.TheoryOfComputation.code.SelfReference.Part2

@[expose] public section

namespace SelfReference

open TuringMachine

variable {Γ : Type}

/-- `IsMinimalTM enc d` says `d` is a *minimal* Turing machine for its language under
the encoding `enc`: no strictly shorter description `d'` recognizes the same
language. Formally, for every `d'`, `|⟨d'⟩| < |⟨d⟩|` implies `L(d') ≠ L(d)`. -/
def IsMinimalTM {Γ : Type} (enc : TMEncoding Γ) (d : TMDescription Γ) : Prop :=
  ∀ d' : TMDescription Γ,
    (enc.encode d').length < (enc.encode d).length → d'.lang ≠ d.lang

/-- `MIN_TM = {⟨M⟩ | M is a minimal TM}`: the set of codes of minimal Turing
machines under the encoding `enc`. This is the language whose
Turing-unrecognizability is shown via the Recursion Theorem. -/
def MIN_TM {Γ : Type} (enc : TMEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : TMDescription Γ, enc.encode d = s ∧ IsMinimalTM enc d}

end SelfReference
