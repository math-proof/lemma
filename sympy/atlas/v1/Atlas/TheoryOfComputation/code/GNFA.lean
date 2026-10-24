/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFA.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.RegularExpressions

open List Set

namespace Sipser

/--
**Definition (Generalized Nondeterministic Empty.Finite Automaton).**
A GNFA over states `Q` and alphabet `σ` is like an NFA, but its transitions
are labeled with *regular expressions* rather than single symbols. For
convenience we assume:

* one `start` state and one `accept` state (distinct, `start_ne_accept`);
* one arrow `δ q q'` (a regex) between every pair of states, with the
  restrictions that no arrow enters the `start` state (`no_enter_start`)
  and no arrow exits the `accept` state (`no_exit_accept`).
-/
structure GNFA (Q : Type*) (σ : Type*) [Fintype Q] where
  start : Q
  accept : Q
  start_ne_accept : start ≠ accept
  δ : Q → Q → RegularExpression σ
  no_enter_start : ∀ q, δ q start = RegularExpression.zero
  no_exit_accept : ∀ q, δ accept q = RegularExpression.zero

namespace GNFA

variable {Q : Type*} {σ : Type*} [Fintype Q]

/--
`AcceptPath G q q' w` says that the word `w` labels a path in the GNFA `G`
from state `q` to state `q'`: either `w = []` and the path is the trivial
self-loop at `q` (`nil`), or `w = w₁ ++ w₂` where some prefix `w₁` reaches
an intermediate state `qmid` and `w₂` is matched by the regex `G.δ qmid q'`
labelling the edge from `qmid` to `q'` (`cons`).
-/
inductive AcceptPath (G : GNFA Q σ) : Q → Q → List σ → Prop where
  | nil (q : Q) : AcceptPath G q q []
  | cons {q qmid q' : Q} {w₁ w₂ : List σ}
    (path : AcceptPath G q qmid w₁)
    (hmatch : w₂ ∈ (G.δ qmid q').matches') :
    AcceptPath G q q' (w₁ ++ w₂)

/-- The GNFA `G` *accepts* the word `w` iff there is an `AcceptPath` from
`G.start` to `G.accept` labelled by `w`. -/
def accepts (G : GNFA Q σ) (w : List σ) : Prop :=
  AcceptPath G G.start G.accept w

/-- The language `L(G)` recognised by the GNFA `G`: the set of all words it
accepts. -/
def language (G : GNFA Q σ) : Language σ :=
  { w | G.accepts w }

/-- Membership in `G.language` unfolds to `G.accepts`; a `simp` rewrite for
convenience. -/
@[simp] theorem mem_language {G : GNFA Q σ} {w : List σ} :
    w ∈ G.language ↔ G.accepts w :=
  Iff.rfl
