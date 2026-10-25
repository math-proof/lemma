/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.BigOperators
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
import Def.v1.Atlas.TheoryOfComputation.code.GeographyGame.Part2
import Structure.v1.Atlas.TheoryOfComputation.code.SpaceComplexity
open Computability
open TuringMachine


namespace SpaceComplexity

section NondeterministicSpace

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- Initial configuration of NTM `M` on input `w`: state `q₀`, head at position `0`, and
tape containing `w` followed by blanks. -/
def NTM.initConfig (M : NTM Q Γ) (w : List Γ) : Config Q Γ where
  state := M.q₀
  headPos := 0
  tape := fun i =>
    if h : 0 ≤ i ∧ i < w.length then
      w.get ⟨i.toNat, by omega⟩
    else M.blank

/-- A configuration is accepting if its state equals `qAccept`. -/
def NTM.isAcceptConfig (M : NTM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qAccept

/-- A configuration is rejecting if its state equals `qReject`. -/
def NTM.isRejectConfig (M : NTM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qReject

/-- A configuration is halting if it is either accepting or rejecting. -/
def NTM.isHaltConfig (M : NTM Q Γ) (c : Config Q Γ) : Prop :=
  M.isAcceptConfig c ∨ M.isRejectConfig c

/-- Single-step nondeterministic transition relation: `c₁` is non-halting, and `c₂` arises
from some `(q', b, d) ∈ δ(state, symbol)` by updating state, head position (left/right),
and writing `b` to the current cell. -/
def NTM.step (M : NTM Q Γ) (c₁ c₂ : Config Q Γ) : Prop :=
  ¬M.isHaltConfig c₁ ∧
  ∃ (q' : Q) (b : Γ) (d : Direction),
    (q', b, d) ∈ M.δ c₁.state (c₁.tape c₁.headPos) ∧
    c₂.state = q' ∧
    c₂.headPos = (match d with
      | Direction.L => c₁.headPos - 1
      | Direction.R => c₁.headPos + 1) ∧
    c₂.tape = Function.update c₁.tape c₁.headPos b

/-- `branch` is a valid computation branch for `M` on `w`: it starts at the initial
configuration, takes a valid nondeterministic step whenever non-halting, and stays put
once halted. -/
def NTM.IsValidBranch (M : NTM Q Γ) (w : List Γ) (branch : ℕ → Config Q Γ) : Prop :=
  branch 0 = M.initConfig w ∧
  ∀ k, (¬M.isHaltConfig (branch k) → M.step (branch k) (branch (k + 1))) ∧
       (M.isHaltConfig (branch k) → branch (k + 1) = branch k)

/-- Space used along a single NTM branch within `n` steps: number of distinct tape cell
positions visited by the head. -/
noncomputable def NTMBranchSpaceUsed {Q Γ : Type}
    (branch : ℕ → Config Q Γ) (n : ℕ) : ℕ :=
  Finset.card ((Finset.range (n + 1)).image (fun k => (branch k).headPos))

/-- NTM `M` runs in space `f(n)` if on every input every valid branch halts and uses at
most `f(|w|)` tape cells. This is Sipser's definition for NSPACE complexity. -/
def NTM.RunsInSpace (M : NTM Q Γ) (f : ℕ → ℕ) : Prop :=
  ∀ (w : List Γ) (branch : ℕ → Config Q Γ),
    M.IsValidBranch w branch →
    (∃ k, M.isHaltConfig (branch k)) ∧
    (∀ k, M.isHaltConfig (branch k) →
      NTMBranchSpaceUsed branch k ≤ f w.length)

/-- `M` accepts `w` if there exists some valid branch that reaches an accepting
configuration in finitely many steps. -/
def NTM.accepts (M : NTM Q Γ) (w : List Γ) : Prop :=
  ∃ (branch : ℕ → Config Q Γ) (k : ℕ),
    M.IsValidBranch w branch ∧ M.isAcceptConfig (branch k)

/-- The language of NTM `M`: all strings over `inputAlpha` that are accepted. -/
def NTM.language (M : NTM Q Γ) : Set (List Γ) :=
  {w | (∀ s ∈ w, s ∈ M.inputAlpha) ∧ M.accepts w}

end NondeterministicSpace

/-- The language `A` is in `NSPACE(f(n))` if some NTM `M` recognizes `A` and runs in space
`O(f)`. Corresponds to Sipser's `NSPACE(f(n))`. -/
def InNSPACE {Γ : Type} (f : ℕ → ℕ) (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : NTM Q Γ),
    M.language = A ∧
    ∃ g : ℕ → ℕ, IsAsympBoundedBy g f ∧ M.RunsInSpace g


/-- A technical lifting lemma: even if the NTM `M` does not a priori have a finite state
type, we can still witness `InNSPACE f A`. (Placeholder; the proof is deferred.) -/
def InPSPACE {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ k : ℕ, InSPACE (fun n => n ^ k) A

/-- `A ∈ NPSPACE` iff `A ∈ NSPACE(n^k)` for some `k`. By Savitch's theorem
NPSPACE = PSPACE. -/
def InNPSPACE {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ k : ℕ, InNSPACE (fun n => n ^ k) A

/-- `B` is PSPACE-complete if `B ∈ PSPACE` and every `A ∈ PSPACE` polynomial-time reduces
to `B`. -/
def IsPSPACEComplete {Γ : Type} (B : Set (List Γ)) : Prop :=
  InPSPACE B ∧ ∀ A : Set (List Γ), InPSPACE A → A ≤ₚ B

variable {α : Type*}

/-- Two equal-length strings `x` and `y` differ in exactly one symbol: there is a unique
position `i` where they disagree, and they agree elsewhere. -/
def DifferInOneSymbol (x y : List α) : Prop :=
  x.length = y.length ∧
  ∃ i, i < x.length ∧
    x[i]? ≠ y[i]? ∧
    ∀ j, j < x.length → j ≠ i → x[j]? = y[j]?

/-- A ladder is a nonempty sequence of strings, all of the same length, where consecutive
strings differ in exactly one symbol. -/
def IsLadder (seq : List (List α)) : Prop :=
  seq ≠ [] ∧
  (∀ w ∈ seq, ∀ w' ∈ seq, w.length = w'.length) ∧
  (∀ (i : ℕ) (hi : i + 1 < seq.length),
    DifferInOneSymbol (seq[i]'(by omega)) (seq[i + 1]'hi))

/-- A ladder in language `L` is a ladder whose every entry belongs to `L`. -/
def IsLadderIn (L : Language α) (seq : List (List α)) : Prop :=
  IsLadder seq ∧ ∀ w ∈ seq, w ∈ L

/-- `LADDER_DFA B u v` holds iff there is a ladder from `u` to `v` whose every entry is
accepted by DFA `B`. This is the language `LADDER_DFA` from Sipser, used as an example of
a problem in `NSPACE(n)` hence in `PSPACE`. -/
def LADDER_DFA {σ : Type*} [Fintype σ] [Fintype α]
    (B : DFA α σ) (u v : List α) : Prop :=
  ∃ seq : List (List α),
    IsLadderIn B.accepts seq ∧
    seq.head? = some u ∧
    seq.getLast? = some v

end SpaceComplexity
