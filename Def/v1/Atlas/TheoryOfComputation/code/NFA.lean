/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NFA.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.EpsilonNFA
import Structure.v1.Atlas.TheoryOfComputation.code.NFA
open Computability Set


namespace Sipser

namespace NFA

variable {Q : Type*} {σ : Type*} [DecidableEq Q]

/-- Convert a Sipser-style `NFA` into Mathlib's `εNFA σ Q` by coercing each
finset of successor states to a `Set`, and packaging the singleton start set
`{q₀}` and accept set `F`. -/
def toεNFA (M : NFA Q σ) : εNFA σ Q where
  step q a := ↑(M.δ q a)
  start := {M.q₀}
  accept := ↑M.accept

/-- The ε-closure of a set of states `S ⊆ Q`: all states reachable from `S`
by zero or more ε-transitions. -/
def εClosure (M : NFA Q σ) (S : Set Q) : Set Q :=
  εNFA.εClosure M.toεNFA S

/-- `M` accepts the input word `w` iff some computation branch of the
underlying ε-NFA reaches an accept state after reading `w`. -/
def accepts (M : NFA Q σ) (w : List σ) : Prop :=
  w ∈ εNFA.accepts M.toεNFA

/-- The language recognized by an NFA `M`: the set of words it accepts. -/
def language (M : NFA Q σ) : Language σ :=
  εNFA.accepts M.toεNFA

end NFA
end Sipser
