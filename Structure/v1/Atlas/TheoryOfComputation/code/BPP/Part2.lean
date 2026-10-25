/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/BPP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Def.v1.Atlas.TheoryOfComputation.code.BPP.Part2


namespace TuringMachine

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-- An abstract "random decider" over alphabet `Γ`: given input `w` and a
sequence of `numBits w.length` random bits it returns a Boolean answer. Used as
an extensional model of a randomized algorithm. -/
structure RandomDecider (Γ : Type) [DecidableEq Γ] where
  numBits : ℕ → ℕ
  decide : (w : List Γ) → (Fin (numBits w.length) → Bool) → Bool

end TuringMachine
