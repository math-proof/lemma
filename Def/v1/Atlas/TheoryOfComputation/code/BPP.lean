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
import Structure.v1.Atlas.TheoryOfComputation.code.BPP


namespace TuringMachine

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-- Advance the PTM `M` by one step from configuration `c` using the given coin
flip: chooses `δ₁` when `coin = true` and `δ₀` otherwise. Halting configurations
(accept/reject) are fixed points. -/
def PTM.stepWithCoin (M : PTM Q Γ) (c : Config Q Γ) (coin : Bool) : Config Q Γ :=
  if c.state = M.qAccept ∨ c.state = M.qReject then c
  else
    let (q', b, d) := if coin then M.δ₁ c.state (c.tape c.headPos)
                              else M.δ₀ c.state (c.tape c.headPos)
    let newHeadPos := match d with
      | Direction.L => c.headPos - 1
      | Direction.R => c.headPos + 1
    ⟨q', newHeadPos, Function.update c.tape c.headPos b⟩

/-- The starting configuration of `M` on input `w`: the head is at position `0`,
the state is `q₀`, and the tape holds the symbols of `w` with blanks elsewhere. -/
def PTM.initConfig (M : PTM Q Γ) (w : List Γ) : Config Q Γ where
  state := M.q₀
  headPos := 0
  tape := fun i =>
    if h : 0 ≤ i ∧ i < w.length then
      w.get ⟨i.toNat, by omega⟩
    else M.blank

/-- Run the PTM `M` on input `w` for `n` steps, consuming the sequence `coins`
of `n` coin flips and returning the resulting configuration. -/
def PTM.runWithCoins (M : PTM Q Γ) (w : List Γ) : (n : ℕ) → (Fin n → Bool) → Config Q Γ
  | 0, _ => M.initConfig w
  | n + 1, coins =>
    let prevCoins : Fin n → Bool := fun i => coins i.castSucc
    let prevConfig := M.runWithCoins w n prevCoins
    M.stepWithCoin prevConfig (coins ⟨n, Nat.lt_succ_of_le le_rfl⟩)

/-- A configuration `c` is accepting for `M` iff its state is `M.qAccept`. -/
def PTM.isAcceptConfig (M : PTM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qAccept

/-- A configuration `c` is rejecting for `M` iff its state is `M.qReject`. -/
def PTM.isRejectConfig (M : PTM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qReject

/-- `M` accepts input `w` along the coin-flip branch `coins` of length `n`. -/
def PTM.acceptsWithCoins (M : PTM Q Γ) (w : List Γ) (n : ℕ)
    (coins : Fin n → Bool) : Prop :=
  M.isAcceptConfig (M.runWithCoins w n coins)

/-- `M` rejects input `w` along the coin-flip branch `coins` of length `n`. -/
def PTM.rejectsWithCoins (M : PTM Q Γ) (w : List Γ) (n : ℕ)
    (coins : Fin n → Bool) : Prop :=
  M.isRejectConfig (M.runWithCoins w n coins)

end TuringMachine
