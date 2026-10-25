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
import Inductive.v1.Atlas.TheoryOfComputation.code.ContextFree


namespace ChomskyNormalForm

variable {T : Type*}

/-- Counts the number of nonterminal symbols occurring in a sentential form. -/
def ntCount {N : Type*} : List (Symbol T N) → ℕ
  | [] => 0
  | Symbol.nonterminal _ :: rest => 1 + ntCount rest
  | Symbol.terminal _ :: rest => ntCount rest

/-- Counts the number of terminal symbols occurring in a sentential form. -/
def tCount {N : Type*} : List (Symbol T N) → ℕ
  | [] => 0
  | Symbol.terminal _ :: rest => 1 + tCount rest
  | Symbol.nonterminal _ :: rest => tCount rest

end ChomskyNormalForm
