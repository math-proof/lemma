/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.BigOperators
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
public import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
public import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
public import Def.v1.Atlas.TheoryOfComputation.code.GeographyGame.Part2
public import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity
public section

open Computability
open TuringMachine


namespace SpaceComplexity

/-- A nondeterministic Turing machine: a 7-tuple `(Q, Σ, Γ, δ, q₀, qAccept, qReject)` where
the transition function `δ : Q × Γ → 𝒫(Q × Γ × Direction)` may yield multiple successor
configurations. -/
structure NTM (Q : Type) (Γ : Type) where
  blank : Γ
  inputAlpha : Set Γ
  blank_not_in_inputAlpha : blank ∉ inputAlpha
  δ : Q → Γ → Set (Q × Γ × Direction)
  q₀ : Q
  qAccept : Q
  qReject : Q
  qReject_ne_qAccept : qReject ≠ qAccept

end SpaceComplexity
