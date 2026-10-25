/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BallotTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic


/-- The combinatorial *ballot count* `ballotCount a b`: the number of
ways to order `a` votes for candidate A and `b` votes for candidate B so that A
strictly leads B throughout the counting. It is defined by the natural
recurrence at the boundary between the +1 and -1 partial sums: zero when
`a = 0`, one when `b = 0` (any ordering of all-A votes is valid), and
`ballotCount a (b+1) + ballotCount (a+1) b` when `a > b`. -/
def ballotCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | Nat.succ _, 0 => 1
  | Nat.succ a, Nat.succ b =>
    if Nat.succ a > Nat.succ b then
      ballotCount a (Nat.succ b) + ballotCount (Nat.succ a) b
    else 0

/-- A *ballot sequence* with `a` A-votes and `b` B-votes: a list of `±1`s of
length `a + b` containing exactly `a` ones and `b` negative ones. Each `+1`
represents a vote for candidate A, each `-1` a vote for B. -/
def IsBallotSeq (a b : ℕ) (l : List Int) : Prop :=
  l.length = a + b ∧
  l.count 1 = a ∧
  l.count (-1) = b ∧
  (∀ v ∈ l, v = 1 ∨ v = -1)

open Classical in
/-- The set of *favorable* ballot sequences for the parameters `a, b`: all
permutations of a list with `a` ones and `b` negative ones such that every
non-empty prefix has strictly positive sum (i.e. candidate A is ahead at every
intermediate counting step). -/
noncomputable def favorableSequences (a b : ℕ) : Finset (List Int) :=
  ((List.replicate a (1 : Int) ++ List.replicate b (-1 : Int)).permutations.toFinset).filter
    (fun l => ∀ k : Fin (a + b), 0 < (l.take (k.val + 1)).sum)

