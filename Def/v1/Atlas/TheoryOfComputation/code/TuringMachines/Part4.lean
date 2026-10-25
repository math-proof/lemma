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
import Inductive.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part2


namespace TuringMachine

open Direction

variable {Q : Type} {Γ : Type} [DecidableEq Q]

open ABSymbol in
/-- The classic non-regular language `A = {a^k b^k | k ≥ 0}` over the alphabet
`{a, b}`. -/
def lang_akbk : Set (List ABSymbol) :=
  {w | ∃ k : ℕ, w = List.replicate k ABSymbol.a ++ List.replicate k ABSymbol.b}

/-- The time-bound function `n · (⌊log₂ n⌋ + 1)`, used as an upper estimate for
`O(n log n)` running times. -/
def nlogn (n : ℕ) : ℕ := n * (Nat.log 2 n + 1)

end TuringMachine
