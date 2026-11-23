/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/BPP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat


public section

namespace TuringMachine

open TuringMachine

/-- A Probabilistic Turing Machine (PTM): a deterministic 1-tape TM augmented with
two transition functions `δ₀` and `δ₁`. At each step the machine flips a fair coin
and uses `δ₀` on outcome `0` and `δ₁` on outcome `1`. -/
structure PTM (Q : Type) (Γ : Type) where
  blank : Γ
  inputAlpha : Set Γ
  blank_not_in_inputAlpha : blank ∉ inputAlpha
  δ₀ : Q → Γ → Q × Γ × Direction
  δ₁ : Q → Γ → Q × Γ × Direction
  q₀ : Q
  qAccept : Q
  qReject : Q
  qReject_ne_qAccept : qReject ≠ qAccept

end TuringMachine
