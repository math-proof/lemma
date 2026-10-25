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
import Instance.v1.Atlas.TheoryOfComputation.code.BPP


namespace TuringMachine

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-- The number of length-`n` coin-flip sequences on which `M` accepts `w`. -/
def PTM.numAccepting (M : PTM Q Γ) (w : List Γ) (n : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun (coins : Fin n → Bool) =>
    M.acceptsWithCoins w n coins))

/-- The number of length-`n` coin-flip sequences on which `M` rejects `w`. -/
def PTM.numRejecting (M : PTM Q Γ) (w : List Γ) (n : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun (coins : Fin n → Bool) =>
    M.rejectsWithCoins w n coins))

/-- The probability that `M` accepts `w` when run for `n` steps with uniform
random coins: `numAccepting / 2^n`. -/
def PTM.acceptProb (M : PTM Q Γ) (w : List Γ) (n : ℕ) : ℚ :=
  (M.numAccepting w n : ℚ) / ((2 : ℚ) ^ n)

/-- The probability that `M` rejects `w` when run for `n` steps with uniform
random coins: `numRejecting / 2^n`. -/
def PTM.rejectProb (M : PTM Q Γ) (w : List Γ) (n : ℕ) : ℚ :=
  (M.numRejecting w n : ℚ) / ((2 : ℚ) ^ n)

/-- `M` decides the language `A` with error at most `ε` using `t (|w|)` coin
flips on input `w`: if `w ∈ A` then `M` rejects `w` with probability `≤ ε`, and
if `w ∉ A` then `M` accepts `w` with probability `≤ ε`. -/
def PTM.decidesWithError (M : PTM Q Γ) (A : Set (List Γ)) (ε : ℚ) (t : ℕ → ℕ) : Prop :=
  (0 ≤ ε) ∧
  (∀ w : List Γ, w ∈ A → M.rejectProb w (t w.length) ≤ ε) ∧
  (∀ w : List Γ, w ∉ A → M.acceptProb w (t w.length) ≤ ε)

/-- `M` runs in time `t`: on every input `w` and every coin sequence of length
`t (|w|)`, the resulting configuration is either accepting or rejecting (i.e.
`M` has halted on every branch within `t (|w|)` steps). -/
def PTM.runsInTime (M : PTM Q Γ) (t : ℕ → ℕ) : Prop :=
  ∀ w : List Γ, ∀ coins : Fin (t w.length) → Bool,
    M.isAcceptConfig (M.runWithCoins w (t w.length) coins) ∨
    M.isRejectConfig (M.runWithCoins w (t w.length) coins)

/-- `M` is polynomial-time: there exist `k` and a runtime bound `t'` with `t'(n) = O(n^k)`
such that `M` halts on every coin-flip branch within `t'(|w|)` steps. -/
def PTM.isPolyTime (M : PTM Q Γ) : Prop :=
  ∃ (k : ℕ) (t' : ℕ → ℕ), M.runsInTime t' ∧ IsBigO t' (fun n => n ^ k)

/-- The complexity class `BPP`: `A ∈ BPP` iff some polynomial-time PTM decides
`A` with two-sided error `ε = 1/3`. -/
def InBPP {Γ : Type} [DecidableEq Γ] (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : PTM Q Γ) (k : ℕ) (t' : ℕ → ℕ),
    M.runsInTime t' ∧
    IsBigO t' (fun n => n ^ k) ∧
    M.decidesWithError A (1 / 3 : ℚ) t'

end TuringMachine
