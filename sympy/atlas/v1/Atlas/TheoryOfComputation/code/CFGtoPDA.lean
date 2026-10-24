/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TheoryOfComputation.code.ContextFree
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.ContextFree

universe u_pda

namespace CFGtoPDA

open ContextFreeGrammar ContextFreeRule

variable {T : Type u_pda}

/-- A language `A ⊆ Σ*` is PDA-recognizable if there exist state and stack alphabet types
together with a pushdown automaton `P = (Q, Σ, Γ, δ, q₀, F)` whose accepted language equals `A`. -/
def IsPDARecognizable (A : Language T) : Prop :=
  ∃ (σ : Type u_pda) (γ : Type u_pda) (P : PDA T σ γ), P.language = A

/-- States of the PDA constructed from a CFG. The PDA has four kinds of states:
* `start` — initial state; pushes the start variable and the bottom-of-stack marker;
* `loop` — main loop that either pops a terminal matching the input, applies a rule
  by replacing a nonterminal on the stack, or transitions to `accept` when the
  bottom-of-stack marker is seen;
* `pushing L` — intermediate states used to push a list `L` of grammar symbols onto
  the stack one symbol per step;
* `accept` — the unique accepting state. -/
inductive QState (T : Type*) (N : Type) where
  | start | loop | pushing : List (Symbol T N) → QState T N | accept

/-- The standard PDA construction from a CFG `g` (Sipser, Lecture 4, "Converting CFGs to PDAs").
The stack alphabet is `Option (Symbol T g.NT)`, where `none` is the bottom-of-stack marker
and `some s` carries a grammar symbol `s`. The PDA:
1. From `start`, pushes the bottom marker and moves into `pushing [S]` where `S = g.initial`.
2. In `loop`, pops a nonterminal `A` and nondeterministically replaces it by the right-hand
   side of any rule `A → r.output` (using the `pushing` states to push symbols one at a time).
3. In `loop`, pops a terminal `t` from the stack only if the next input symbol matches `t`.
4. When the bottom marker is exposed in `loop`, moves to `accept`. -/
def toPDA (g : ContextFreeGrammar T) :
    PDA T (QState T g.NT) (Option (Symbol T g.NT)) where
  start := QState.start
  accept := {QState.accept}
  step := fun q a pop =>
    match q, a, pop with
    | QState.start, none, none =>
        {(QState.pushing [Symbol.nonterminal g.initial], some none)}
    | QState.loop, none, some (some (Symbol.nonterminal A)) =>
        { p | ∃ r ∈ g.rules, r.input = A ∧
          p = (QState.pushing r.output.reverse, none) }
    | QState.loop, some a, some (some (Symbol.terminal t)) =>
        { p | a = t ∧ p = (QState.loop, none) }
    | QState.loop, none, some none =>
        {(QState.accept, none)}
    | QState.pushing (s :: rest), none, none =>
        {(QState.pushing rest, some (some s))}
    | QState.pushing [], none, none =>
        {(QState.loop, none)}
    | _, _, _ => ∅

variable {g : ContextFreeGrammar T}

set_option maxRecDepth 1024 in


/-- `DerivesIn' g n γ δ` means `γ ⇒ⁿ δ` in `g`: there is a derivation of length exactly
`n` from `γ` to `δ` using the rules of `g`. -/
inductive DerivesIn' (g : ContextFreeGrammar T) :
    ℕ → List (Symbol T g.NT) → List (Symbol T g.NT) → Prop where
  | refl (γ) : DerivesIn' g 0 γ γ
  | step {n γ δ τ} : g.Produces γ δ → DerivesIn' g n δ τ → DerivesIn' g (n + 1) γ τ


/-- `StepCount M n c₁ c₂` means the PDA `M` reaches configuration `c₂` from `c₁` in
exactly `n` steps. This is the step-counted refinement of `M.Reaches`. -/
inductive StepCount (M : PDA T σ γ₁) :
    ℕ → PDA.Config (α := T) (σ := σ) (γ := γ₁) →
    PDA.Config (α := T) (σ := σ) (γ := γ₁) → Prop where
  | refl (c) : StepCount M 0 c c
  | step {n c1 c2 c3} : M.Step c1 c2 → StepCount M n c2 c3 → StepCount M (n + 1) c1 c3
