/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Ring
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Instance.v1.Atlas.TheoryOfComputation.code.LogSpace
open SpaceComplexity
open TuringMachine


namespace LogSpace

/-- Convert an ordinary Turing-machine configuration into the log-space
configuration view by taking the input head position to be `|c.headPos|`,
initializing the work head to `0`, and copying the tape as the work tape. -/
def LogSpaceConfig.ofConfig
    (c : TuringMachine.Config Q Γ) : LogSpaceConfig Q Γ where
  state := c.state
  inputHeadPos := c.headPos.natAbs
  workHeadPos := 0
  workTape := fun i => c.tape (Int.ofNat i)

/-- The complexity class `L = SPACE(log n)`: `A ∈ L` iff `A` is decided by some
deterministic TM in space `O(log n)`. -/
def InL {Γ : Type} (A : Set (List Γ)) : Prop :=
  InSPACE log A

/-- The complexity class `NL = NSPACE(log n)`: `A ∈ NL` iff `A` is decided by
some nondeterministic TM in space `O(log n)`. -/
def InNL {Γ : Type} (A : Set (List Γ)) : Prop :=
  InNSPACE log A

/-- `coNSPACE(f)`: `A ∈ coNSPACE(f)` iff the complement of `A` lies in
`NSPACE(f)`. -/
def InCoNSPACE {Γ : Type} (f : ℕ → ℕ) (A : Set (List Γ)) : Prop :=
  InNSPACE f Aᶜ

/-- The class `coNL = coNSPACE(log n)`: `A ∈ coNL` iff `Aᶜ ∈ NL`. -/
def InCoNL {Γ : Type} (A : Set (List Γ)) : Prop :=
  InCoNSPACE log A

/-- `IsAtLeastLog f` asserts that `f` grows at least as fast as `log₂`, i.e.
`log₂ n ≤ f n` for every `n`. This is the standard hypothesis under which
Immerman–Szelepcsényi gives `NSPACE(f) = coNSPACE(f)`. -/
def IsAtLeastLog (f : ℕ → ℕ) : Prop :=
  ∀ n, Nat.log 2 n ≤ f n

end LogSpace
