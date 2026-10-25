/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.ContextFree.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.ContextFree
import Inductive.v1.Atlas.TheoryOfComputation.code.CFGtoPDA
universe u_pda


namespace CFGtoPDA

open ContextFreeGrammar ContextFreeRule

variable {T : Type u_pda}

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

end CFGtoPDA
