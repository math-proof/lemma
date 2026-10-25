/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.ContextFree.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.ContextFree
import Def.v1.Atlas.TheoryOfComputation.code.CFGtoPDA
universe u_pda


namespace CFGtoPDA

open ContextFreeGrammar ContextFreeRule

variable {T : Type u_pda}

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

end CFGtoPDA
