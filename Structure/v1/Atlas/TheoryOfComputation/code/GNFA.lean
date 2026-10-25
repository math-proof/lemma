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

end Sipser
