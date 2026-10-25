/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.BigOperators
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
import Def.v1.Atlas.TheoryOfComputation.code.GeographyGame.Part2
open Computability
open TuringMachine


namespace SpaceComplexity

/-- Asymptotic upper bound: `g` is `O(f)` in the sense that there exist constants `c > 0` and
`n₀` such that `g n ≤ c * f n` for all `n ≥ n₀`. -/
def IsAsympBoundedBy (g f : ℕ → ℕ) : Prop :=
  ∃ (c : ℕ) (n₀ : ℕ), 0 < c ∧ ∀ n, n₀ ≤ n → g n ≤ c * f n

/-- Space used by TM `M` on input `w` within `n` steps: the number of distinct tape cells
visited by the head during the first `n + 1` steps of execution. -/
noncomputable def TMSpaceUsed {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (w : List Γ) (n : ℕ) : ℕ :=
  Finset.card ((Finset.range (n + 1)).image (fun k => (M.runOnInput w k).headPos))

/-- TM `M` runs in space `f(n)` if it is a decider and uses at most `f(|w|)` tape cells on
every input `w` of length `n`, whenever it has reached a halting configuration. -/
def TMRunsInSpace {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (f : ℕ → ℕ) : Prop :=
  M.isDecider ∧
  ∀ (w : List Γ) (n : ℕ), M.isHaltConfig (M.runOnInput w n) →
    TMSpaceUsed M w n ≤ f w.length

/-- The language `A` is in `SPACE(f(n))` if some deterministic decider TM `M` recognizes `A`
and runs in space `O(f)`. Corresponds to Sipser's `SPACE(f(n))`. -/
def InSPACE {Γ : Type} (f : ℕ → ℕ) (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : TM Q Γ),
    M.language = A ∧
    ∃ g : ℕ → ℕ, IsAsympBoundedBy g f ∧ TMRunsInSpace M g

end SpaceComplexity
