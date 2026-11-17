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
public import Structure.v1.Atlas.TheoryOfComputation.code.ContextFree

@[expose] public section


namespace ChomskyNormalForm

variable {T : Type*}

namespace PDA

variable {α : Type u} {σ : Type v} {γ : Type w}

variable (M : PDA α σ γ)

/-- An *instantaneous configuration* of a PDA: a triple `(q, input, stack)`
recording the current state, the remaining input to be read, and the current
stack contents (top at the head of the list). -/
abbrev Config := σ × List α × List γ

end PDA
end ChomskyNormalForm
