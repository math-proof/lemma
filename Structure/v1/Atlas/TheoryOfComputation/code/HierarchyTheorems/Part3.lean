/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.DFA
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
public import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
public import Def.v1.Atlas.TheoryOfComputation.code.HierarchyTheorems.Part3


public section

namespace HierarchyTheorems

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/--
A **nondeterministic oracle Turing machine**: like `OracleTM` but the transition
function `δ` returns a *set* of possible next moves at each step. Used to define
NP-with-oracle complexity classes.
-/
structure OracleNTM (Q : Type) (Γ : Type) where
  blank : Γ
  inputAlpha : Set Γ
  blank_not_in_inputAlpha : blank ∉ inputAlpha
  δ : Q → Γ → Bool → Set (Q × Γ × Direction)
  q₀ : Q
  qAccept : Q
  qReject : Q
  qReject_ne_qAccept : qReject ≠ qAccept
  qQuery : Q
  oracle : Set (List Γ)

end HierarchyTheorems
