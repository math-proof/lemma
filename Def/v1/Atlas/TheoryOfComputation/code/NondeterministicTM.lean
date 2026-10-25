/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NondeterministicTM.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import Structure.v1.Atlas.TheoryOfComputation.code.NondeterministicTM


namespace TuringMachine

open Direction

variable {Q : Type} {Γ : Type}

/-- Apply a specific nondeterministic `choice = (q', b, d)` to configuration `c`:
write `b`, move the head in direction `d`, and transition to state `q'`. -/
def NTM.stepWith (_M : NTM Q Γ) (c : Config Q Γ) (choice : Q × Γ × Direction) :
    Config Q Γ :=
  let (q', b, d) := choice
  { state := q'
    headPos := match d with
      | Direction.L => c.headPos - 1
      | Direction.R => c.headPos + 1
    tape := Function.update c.tape c.headPos b }

/-- The starting configuration of NTM `M` on input `w`: state `q₀`, head at
position `0`, tape containing `w` followed by blanks. -/
def NTM.initConfig (M : NTM Q Γ) (w : List Γ) : Config Q Γ where
  state := M.q₀
  headPos := 0
  tape := fun i =>
    if h : 0 ≤ i ∧ i < w.length then
      w.get ⟨i.toNat, by omega⟩
    else M.blank

/-- `c` is an accepting configuration of NTM `M` (state equals `qAccept`). -/
def NTM.isAcceptConfig (M : NTM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qAccept

/-- `c` is a rejecting configuration of NTM `M` (state equals `qReject`). -/
def NTM.isRejectConfig (M : NTM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qReject

/-- `c` is a halting configuration of NTM `M`: either accepting or rejecting. -/
def NTM.isHaltConfig (M : NTM Q Γ) (c : Config Q Γ) : Prop :=
  M.isAcceptConfig c ∨ M.isRejectConfig c

/-- `branch : ℕ → Config Q Γ` is a valid computation branch of `M` on input `w`:
it starts in `initConfig w`, stays put at halting configurations, and at each
non-halting step picks some allowed nondeterministic transition. -/
def NTM.IsBranch (M : NTM Q Γ) (w : List Γ) (branch : ℕ → Config Q Γ) : Prop :=
  branch 0 = M.initConfig w ∧
  (∀ n, M.isHaltConfig (branch n) → branch (n + 1) = branch n) ∧
  (∀ n, ¬M.isHaltConfig (branch n) →
    ∃ choice ∈ M.δ (branch n).state ((branch n).tape (branch n).headPos),
      branch (n + 1) = M.stepWith (branch n) choice)

/-- A branch halts with output `v`: it reaches an accepting configuration whose
tape contents (from position `0`) equal `v`, followed by blanks. -/
def NTM.branchHaltsWithOutput (M : NTM Q Γ)
    (branch : ℕ → Config Q Γ) (v : List Γ) : Prop :=
  ∃ n, M.isAcceptConfig (branch n) ∧
    (∀ (i : ℕ) (hi : i < v.length), (branch n).tape (↑i) = v.get ⟨i, hi⟩) ∧
    (∀ i : ℕ, i ≥ v.length → (branch n).tape (↑i) = M.blank)

/-- A branch rejects: it reaches a rejecting configuration at some step `n`. -/
def NTM.branchRejects (M : NTM Q Γ) (branch : ℕ → Config Q Γ) : Prop :=
  ∃ n, M.isRejectConfig (branch n)

/-- NTM `M` computes the function `f : Σ* → Σ*` (Sipser, Lecture 20):
on every input `w`, every branch either halts with `f w` on the tape or rejects,
and at least one branch does not reject. -/
def NTMComputes (M : NTM Q Γ) (f : List Γ → List Γ) : Prop :=
  ∀ w : List Γ,

    (∀ branch : ℕ → Config Q Γ, M.IsBranch w branch →
      M.branchHaltsWithOutput branch (f w) ∨ M.branchRejects branch) ∧

    (∃ branch : ℕ → Config Q Γ, M.IsBranch w branch ∧ ¬M.branchRejects branch)

end TuringMachine
