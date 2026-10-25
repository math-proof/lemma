/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Structure.v1.Atlas.TheoryOfComputation.code.HierarchyTheorems.Part3


namespace HierarchyTheorems

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/--
Single-step relation for an oracle NTM: `M.step c₁ c₂` holds when `c₂` is one of
the configurations reachable from `c₁` in one step (or `c₂ = c₁` if `c₁` is a
halt configuration). Membership of `queryTape` in `oracle` is consulted whenever
the state is `qQuery`.
-/
noncomputable def OracleNTM.step (M : OracleNTM Q Γ) (c₁ c₂ : OracleConfig Q Γ) : Prop :=
  if c₁.state = M.qAccept ∨ c₁.state = M.qReject then c₂ = c₁
  else
    let oracleAnswer : Bool :=
      if c₁.state = M.qQuery then
        Classical.propDecidable (c₁.queryTape ∈ M.oracle) |>.decide
      else false
    ∃ q' b d, (q', b, d) ∈ M.δ c₁.state (c₁.tape c₁.headPos) oracleAnswer ∧
      let newHeadPos := match d with
        | Direction.L => c₁.headPos - 1
        | Direction.R => c₁.headPos + 1
      c₂ = ⟨q', newHeadPos, Function.update c₁.tape c₁.headPos b, c₁.queryTape⟩

/-- Initial configuration of an oracle NTM on input `w` (analogous to `OracleTM.initConfig`). -/
def OracleNTM.initConfig (M : OracleNTM Q Γ) (w : List Γ) : OracleConfig Q Γ where
  state := M.q₀
  headPos := 0
  tape := fun i =>
    if h : 0 ≤ i ∧ i < w.length then
      w.get ⟨i.toNat, by omega⟩
    else M.blank
  queryTape := []

/-- A configuration is a **halt configuration** if its state is `qAccept` or `qReject`. -/
def OracleNTM.isHaltConfig (M : OracleNTM Q Γ) (c : OracleConfig Q Γ) : Prop :=
  c.state = M.qAccept ∨ c.state = M.qReject

/-- A configuration is an **accept configuration** if its state equals `qAccept`. -/
def OracleNTM.isAcceptConfig (M : OracleNTM Q Γ) (c : OracleConfig Q Γ) : Prop :=
  c.state = M.qAccept

/--
`M.accepts w` if there exists some nondeterministic computation **branch** of `M`
on `w` (a finite sequence of valid step-related configurations starting from
`M.initConfig w`) ending in an accept configuration.
-/
noncomputable def OracleNTM.accepts (M : OracleNTM Q Γ) (w : List Γ) : Prop :=
  ∃ (n : ℕ) (branch : Fin (n + 1) → OracleConfig Q Γ),
    branch ⟨0, Nat.zero_lt_succ n⟩ = M.initConfig w ∧
    (∀ (i : Fin n), M.step (branch i.castSucc) (branch i.succ)) ∧
    M.isAcceptConfig (branch ⟨n, Nat.lt_succ_of_le le_rfl⟩)

/-- The language of an oracle NTM `M` is the set of strings it accepts. -/
noncomputable def OracleNTM.language (M : OracleNTM Q Γ) : Set (List Γ) :=
  {w | M.accepts w}

/--
An oracle NTM `M` is a **decider** if every nondeterministic branch from the
initial configuration eventually reaches a halt configuration.
-/
noncomputable def OracleNTM.isDecider (M : OracleNTM Q Γ) : Prop :=
  ∀ w : List Γ, ∀ (n : ℕ) (branch : Fin (n + 1) → OracleConfig Q Γ),
    0 < n →
    branch ⟨0, Nat.zero_lt_succ n⟩ = M.initConfig w →
    (∀ (i : Fin n), M.step (branch i.castSucc) (branch i.succ)) →
    ∃ k : Fin (n + 1), M.isHaltConfig (branch k)

/-- `M.decides B` if `M` is a decider whose language is `B`. -/
noncomputable def OracleNTM.decides (M : OracleNTM Q Γ) (B : Set (List Γ)) : Prop :=
  M.isDecider ∧ M.language = B

/--
`M.runsInTime t` if on every input `w` and every valid branch of length
`k ≤ t(|w|)`, the configuration at step `k` is a halt configuration.
-/
noncomputable def OracleNTM.runsInTime (M : OracleNTM Q Γ) (t : ℕ → ℕ) : Prop :=
  ∀ w : List Γ,
    ∀ (k : ℕ) (branch : Fin (k + 1) → OracleConfig Q Γ),
      0 < k →
      branch ⟨0, Nat.zero_lt_succ k⟩ = M.initConfig w →
      (∀ (i : Fin k), M.step (branch i.castSucc) (branch i.succ)) →
      k ≤ t w.length →
      M.isHaltConfig (branch ⟨k, Nat.lt_succ_of_le le_rfl⟩)

/--
`InPWithOracle A B` says `B ∈ P^A`: some deterministic oracle TM with oracle `A`
decides `B` in polynomial time `n^k`.
-/
def InPWithOracle {Γ : Type} (A B : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : OracleTM Q Γ),
    M.oracle = A ∧ M.decides B ∧ ∃ k : ℕ, M.runsInTime (fun n => n ^ k)

/--
`InNPWithOracle A B` says `B ∈ NP^A`: some nondeterministic oracle TM with
oracle `A` decides `B` in polynomial time `n^k`.
-/
def InNPWithOracle {Γ : Type} (A B : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : OracleNTM Q Γ),
    M.oracle = A ∧ M.decides B ∧ ∃ k : ℕ, M.runsInTime (fun n => n ^ k)

/-- The complexity class `P^A`: all languages decidable in P with oracle `A`. -/
def ClassPWithOracle {Γ : Type} (A : Set (List Γ)) : Set (Set (List Γ)) :=
  {B | InPWithOracle A B}

/-- The complexity class `NP^A`: all languages decidable in NP with oracle `A`. -/
def ClassNPWithOracle {Γ : Type} (A : Set (List Γ)) : Set (Set (List Γ)) :=
  {B | InNPWithOracle A B}

/-- `InPSPACE A` (in this namespace) reuses the definition `SpaceComplexity.InPSPACE`. -/
def InPSPACE {Γ : Type} (A : Set (List Γ)) : Prop :=
  SpaceComplexity.InPSPACE A

/-- `InNPSPACE A` (in this namespace) reuses the definition `SpaceComplexity.InNPSPACE`. -/
def InNPSPACE {Γ : Type} (A : Set (List Γ)) : Prop :=
  SpaceComplexity.InNPSPACE A

/--
`TQBF` is the language of *true* quantified Boolean formulae under encoding `enc`
(a wrapper over `SpaceComplexity.tqbfLanguage`). `TQBF` is the canonical
PSPACE-complete language used here as an oracle.
-/
def TQBF {Γ : Type} [Inhabited Γ] (enc : SpaceComplexity.QBFEncoding Γ) :
    Set (List Γ) :=
  SpaceComplexity.tqbfLanguage enc

end HierarchyTheorems
