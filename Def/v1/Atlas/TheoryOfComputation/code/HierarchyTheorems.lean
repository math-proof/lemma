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


namespace HierarchyTheorems

open TuringMachine

/--
A function `f : ℕ → ℕ` is **time constructible** if there exists a Turing machine `M`
which is a decider, runs in some time `t'`, with `t' = O(f)`. This is the standard
hypothesis under which the Time Hierarchy Theorem is stated.
-/
def IsTimeConstructible (f : ℕ → ℕ) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (Γ : Type) (M : TM Q Γ) (t' : ℕ → ℕ),
    M.isDecider ∧ M.runsInTime t' ∧ IsBigO t' f

/--
`IsLittleO g f` says `g(n) = o(f(n))`: for every positive constant `c`, there is
some `n₀` such that `c · g(n) < f(n)` for all `n ≥ n₀`.
-/
def IsLittleO (g f : ℕ → ℕ) : Prop :=
  ∀ c : ℕ, 0 < c → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → c * g n < f n

/--
`IsAsympDominated g f` is the little-`o` relation on `ℕ → ℕ`: for every constant
`c > 0` there exists `n₀` such that `c · g(n) < f(n)` for all `n ≥ n₀`.
Used to express `g = o(f)` in the Space Hierarchy Theorem.
-/
def IsAsympDominated (g f : ℕ → ℕ) : Prop :=
  ∀ (c : ℕ), 0 < c → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → c * g n < f n

/--
`InSPACEo f A` says the language `A` is decidable in space `o(f(n))`: some TM
recognizes `A` and runs in space `g` with `g = o(f)`. This is the class
`SPACE(o(f(n)))` appearing in the Space Hierarchy Theorem.
-/
def InSPACEo {Γ : Type} (f : ℕ → ℕ) (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : TM Q Γ),
    M.language = A ∧
    ∃ g : ℕ → ℕ, IsAsympDominated g f ∧ TMRunsInSpace M g

/--
A function `f : ℕ → ℕ` is **space constructible** if there is a TM decider `M`
whose space usage on every input of length `n` equals `f(n)` exactly once it
halts. This is the standard hypothesis for the Space Hierarchy Theorem.
-/
def SpaceConstructible (f : ℕ → ℕ) : Prop :=
  ∃ (Q Γ : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : TM Q Γ),
    M.isDecider ∧
    ∀ (w : List Γ) (n : ℕ), M.isHaltConfig (M.runOnInput w n) →
      TMSpaceUsed M w n = f w.length

end HierarchyTheorems
