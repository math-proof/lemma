/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Complexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import Def.v1.Atlas.TheoryOfComputation.code.NondeterministicTM
import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum


namespace TuringMachine

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- A single nondeterministic step of `M`: `c₂` is a possible successor of `c₁`,
selected from the set of transitions `δ c₁.state (read symbol)`. Halting
configurations are fixed points. -/
def NTM.step (M : NTM Q Γ) (c₁ c₂ : Config Q Γ) : Prop :=
  if c₁.state = M.qAccept ∨ c₁.state = M.qReject then c₂ = c₁
  else
    ∃ q' b d, (q', b, d) ∈ M.δ c₁.state (c₁.tape c₁.headPos) ∧
      let newHeadPos := match d with
        | Direction.L => c₁.headPos - 1
        | Direction.R => c₁.headPos + 1
      c₂ = ⟨q', newHeadPos, Function.update c₁.tape c₁.headPos b⟩

/-- NTM acceptance: `M` accepts `w` iff there is some finite computation branch
of length `n + 1` starting from `M.initConfig w`, with each step a valid
nondeterministic transition, ending in an accepting configuration. -/
def NTM.accepts (M : NTM Q Γ) (w : List Γ) : Prop :=
  ∃ (n : ℕ) (branch : Fin (n + 1) → Config Q Γ),
    branch ⟨0, Nat.zero_lt_succ n⟩ = M.initConfig w ∧
    (∀ (i : Fin n), M.step (branch i.castSucc) (branch i.succ)) ∧
    M.isAcceptConfig (branch ⟨n, Nat.lt_succ_of_le le_rfl⟩)

/-- The language recognized by NTM `M`: the set of strings it accepts. -/
def NTM.language (M : NTM Q Γ) : Set (List Γ) :=
  {w | M.accepts w}

/-- An NTM is a decider if every computation branch on every input halts in
finitely many steps. -/
def NTM.isDecider (M : NTM Q Γ) : Prop :=
  ∀ w : List Γ, ∀ (n : ℕ) (branch : Fin (n + 1) → Config Q Γ),
    0 < n →
    branch ⟨0, Nat.zero_lt_succ n⟩ = M.initConfig w →
    (∀ (i : Fin n), M.step (branch i.castSucc) (branch i.succ)) →
    ∃ k : Fin (n + 1), M.isHaltConfig (branch k)

/-- `M` decides `A` iff it is a decider and its language equals `A`. -/
def NTM.decides (M : NTM Q Γ) (A : Set (List Γ)) : Prop :=
  M.isDecider ∧ M.language = A

/-- A deterministic TM runs in time `t` if it halts on every input `w` within
`t (|w|)` steps. -/
def TM.runsInTime (M : TM Q Γ) (t : ℕ → ℕ) : Prop :=
  ∀ w : List Γ, M.isHaltConfig (M.runOnInput w (t w.length))

/-- An NTM runs in time `t` if every branch of length at most `t (|w|)` reaches
a halting configuration on input `w`. -/
def NTM.runsInTime (M : NTM Q Γ) (t : ℕ → ℕ) : Prop :=
  ∀ w : List Γ,
    ∀ (k : ℕ) (branch : Fin (k + 1) → Config Q Γ),
      0 < k →
      branch ⟨0, Nat.zero_lt_succ k⟩ = M.initConfig w →
      (∀ (i : Fin k), M.step (branch i.castSucc) (branch i.succ)) →
      k ≤ t w.length →
      M.isHaltConfig (branch ⟨k, Nat.lt_succ_of_le le_rfl⟩)

/-- `f = O(g)`: there exist constants `c > 0` and `n₀` such that `f n ≤ c · g n`
for all `n ≥ n₀`. -/
def IsBigO (f g : ℕ → ℕ) : Prop :=
  ∃ c n₀ : ℕ, 0 < c ∧ ∀ n, n₀ ≤ n → f n ≤ c * g n

/-- `A ∈ TIME(t)`: some deterministic TM decides `A` in time `O(t)`. -/
def InTIME (t : ℕ → ℕ) {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : TM Q Γ) (t' : ℕ → ℕ),
    M.decides A ∧ M.runsInTime t' ∧ IsBigO t' t

/-- `A ∈ NTIME(t)`: some nondeterministic TM decides `A` in time `O(t)`. -/
def InNTIME (t : ℕ → ℕ) {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : NTM Q Γ) (t' : ℕ → ℕ),
    M.decides A ∧ M.runsInTime t' ∧ IsBigO t' t

/-- The complexity class P: `A ∈ P` iff `A ∈ TIME(n^k)` for some `k`. -/
def InP {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ k : ℕ, InTIME (fun n => n ^ k) A

/-- The complexity class NP: `A ∈ NP` iff `A ∈ NTIME(n^k)` for some `k`. -/
def InNP {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ k : ℕ, InNTIME (fun n => n ^ k) A

/-- The complexity class EXPTIME: deciders running in time `2^{n^k}` for some `k`. -/
def InEXPTIME {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ k : ℕ, InTIME (fun n => 2 ^ (n ^ k)) A

/-- A function `f : Σ* → Σ*` is polynomial-time computable: there exists a
deterministic TM `F` that, on input `w`, halts within `|w|^k` steps with `f w`
written on the prefix of its tape. -/
def IsPolyTimeComputableFunction {Γ : Type} (f : List Γ → List Γ) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (F : TM Q Γ) (k : ℕ),
    (∀ w : List Γ, ∃ n : ℕ,
      n ≤ (fun m => m ^ k) w.length ∧
      F.isHaltConfig (F.runOnInput w n) ∧
      Config.readTape (F.runOnInput w n) (f w).length = f w)

/-- Polynomial-time mapping reducibility `A ≤ₚ B`: there is a polynomial-time
computable `f` with `w ∈ A ↔ f w ∈ B`. -/
def PolyReducible {Γ : Type} (A B : Set (List Γ)) : Prop :=
  ∃ f : List Γ → List Γ,
    IsPolyTimeComputableFunction f ∧
    ∀ w : List Γ, w ∈ A ↔ f w ∈ B

end TuringMachine
