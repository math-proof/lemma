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
import Structure.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part2


namespace TuringMachine

open Direction

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- One computation step of `M`: if the current state is `qAccept` or `qReject`
the configuration is fixed; otherwise apply `δ` to write a new symbol, move the
head left or right, and update the state. -/
def TM.step (M : TM Q Γ) (c : Config Q Γ) : Config Q Γ :=
  if c.state = M.qAccept ∨ c.state = M.qReject then c
  else
    let (q', b, d) := M.δ c.state (c.tape c.headPos)
    { state := q'
      headPos := match d with
        | Direction.L => c.headPos - 1
        | Direction.R => c.headPos + 1
      tape := Function.update c.tape c.headPos b }

/-- The initial configuration of `M` on input `w`: state `q₀`, head at position
`0`, and the tape containing `w` at positions `0, …, |w|-1` with blanks elsewhere. -/
def TM.initConfig (M : TM Q Γ) (w : List Γ) : Config Q Γ where
  state := M.q₀
  headPos := 0
  tape := fun i =>
    if h : 0 ≤ i ∧ i < w.length then
      w.get ⟨i.toNat, by omega⟩
    else M.blank

/-- Iterate `M.step` starting from configuration `c` for `n` steps. -/
def TM.run (M : TM Q Γ) (c : Config Q Γ) : ℕ → Config Q Γ
  | 0 => c
  | n + 1 => M.step (M.run c n)

/-- The configuration of `M` after running `n` steps on input `w`, starting
from `M.initConfig w`. -/
def TM.runOnInput (M : TM Q Γ) (w : List Γ) (n : ℕ) : Config Q Γ :=
  M.run (M.initConfig w) n

/-- A configuration is "accepting" if its state equals `M.qAccept`. -/
def TM.isAcceptConfig (M : TM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qAccept

/-- A configuration is "rejecting" if its state equals `M.qReject`. -/
def TM.isRejectConfig (M : TM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qReject

/-- A configuration is "halting" if it is either accepting or rejecting. -/
def TM.isHaltConfig (M : TM Q Γ) (c : Config Q Γ) : Prop :=
  M.isAcceptConfig c ∨ M.isRejectConfig c

/-- `M` accepts the input `w` if at some step `n` the computation enters
`qAccept`. -/
def TM.accepts (M : TM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ, M.isAcceptConfig (M.runOnInput w n)

/-- `M` rejects the input `w` (by halting) if at some step `n` the computation
enters `qReject`. -/
def TM.rejects (M : TM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ, M.isRejectConfig (M.runOnInput w n)

/-- `M` halts on input `w` if it reaches a halting (accept or reject)
configuration after some number of steps. -/
def TM.halts (M : TM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ, M.isHaltConfig (M.runOnInput w n)

/-- The language `L(M)` recognized by `M`: the set of inputs `w` that `M`
accepts. -/
def TM.language (M : TM Q Γ) : Set (List Γ) :=
  {w | M.accepts w}

/-- `c₁` yields `c₂` in one step: `c₁` is not a halting configuration and
`M.step c₁ = c₂`. -/
def TM.yields (M : TM Q Γ) (c₁ c₂ : Config Q Γ) : Prop :=
  ¬M.isHaltConfig c₁ ∧ M.step c₁ = c₂

/-- The reflexive-transitive closure of one-step yielding: `c₁` reaches `c₂`
after some finite number of computation steps. -/
def TM.yieldsMulti (M : TM Q Γ) (c₁ c₂ : Config Q Γ) : Prop :=
  ∃ n : ℕ, M.run c₁ n = c₂

/-- `M` has an accepting computation history on `w`: at some step `n` the
configuration is in `qAccept`. (Same as `M.accepts w`.) -/
def TM.hasAcceptingHistory (M : TM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ, M.isAcceptConfig (M.runOnInput w n)

/-- `M` is a decider: it halts on every input (never loops forever). -/
def TM.isDecider (M : TM Q Γ) : Prop :=
  ∀ w : List Γ, M.halts w

/-- A language `A` is Turing-recognizable if there is some Turing machine `M`
with `L(M) = A`. -/
def IsTuringRecognizable (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : TM Q Γ), M.language = A

/-- A language `A` is Turing-decidable if some TM decider `M` (a TM that halts
on every input) satisfies `L(M) = A`. -/
def IsTuringDecidable (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : TM Q Γ), M.isDecider ∧ M.language = A

/-- `M` decides `A` if `M` is a decider and `L(M) = A`. -/
def TM.decides (M : TM Q Γ) (A : Set (List Γ)) : Prop :=
  M.isDecider ∧ M.language = A

end TuringMachine
