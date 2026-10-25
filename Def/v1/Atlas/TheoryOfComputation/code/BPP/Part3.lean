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
import Structure.v1.Atlas.TheoryOfComputation.code.BPP.Part2


namespace TuringMachine

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-- A `RandomDecider` decides `A` with two-sided error `≤ 1/3`: for `w ∈ A` the
fraction of random strings on which it answers `false` is at most `1/3`, and
symmetrically for `w ∉ A`. -/
def RandomDecider.decidesWithBoundedError {Γ : Type} [DecidableEq Γ]
    (rd : RandomDecider Γ) (A : Set (List Γ)) : Prop :=
  (∀ w : List Γ, w ∈ A →
    ((Finset.univ.filter (fun r : Fin (rd.numBits w.length) → Bool =>
        rd.decide w r = false)).card : ℚ) / (2 : ℚ) ^ rd.numBits w.length ≤ 1 / 3) ∧
  (∀ w : List Γ, w ∉ A →
    ((Finset.univ.filter (fun r : Fin (rd.numBits w.length) → Bool =>
        rd.decide w r = true)).card : ℚ) / (2 : ℚ) ^ rd.numBits w.length ≤ 1 / 3)

/-- A `RandomDecider` is polynomial-time if its number of random bits is
polynomially bounded in the input length. -/
def RandomDecider.isPolyTime {Γ : Type} [DecidableEq Γ]
    (rd : RandomDecider Γ) : Prop :=
  ∃ k : ℕ, IsBigO rd.numBits (fun n => n ^ k)

end TuringMachine
