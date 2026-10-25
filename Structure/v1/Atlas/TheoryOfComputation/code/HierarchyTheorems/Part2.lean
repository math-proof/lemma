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
import Def.v1.Atlas.TheoryOfComputation.code.HierarchyTheorems.Part2


namespace HierarchyTheorems

open TuringMachine

/--
A **deterministic oracle Turing machine** over state set `Q` and tape alphabet `Γ`.
Beyond the usual TM data (blank symbol, input alphabet, transition `δ`, start state,
accept/reject states), the machine has a distinguished query state `qQuery` and an
oracle `oracle ⊆ List Γ`. The transition function takes an extra `Bool` reading the
oracle's answer to the current query tape, so the machine can consult oracle
membership in a single step.
-/
structure OracleTM (Q : Type) (Γ : Type) where
  blank : Γ
  inputAlpha : Set Γ
  blank_not_in_inputAlpha : blank ∉ inputAlpha
  δ : Q → Γ → Bool → Q × Γ × Direction
  q₀ : Q
  qAccept : Q
  qReject : Q
  qReject_ne_qAccept : qReject ≠ qAccept
  qQuery : Q
  oracle : Set (List Γ)

/--
A configuration of an oracle TM: the current state, head position on the
two-way infinite tape, the tape contents, and the contents of the auxiliary
**query tape** which holds the string to be tested against the oracle.
-/
structure OracleConfig (Q : Type) (Γ : Type) where
  state : Q
  headPos : ℤ
  tape : ℤ → Γ
  queryTape : List Γ

end HierarchyTheorems
