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
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.SpaceComplexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Complexity
open SpaceComplexity
open TuringMachine

namespace LogSpace

/-- Base-2 logarithm on `ℕ`, used as the canonical space bound for the class `L = SPACE(log n)`. -/
def log : ℕ → ℕ := Nat.log 2

/-- A log-space Turing machine configuration `(q, p_1, p_2, t)` consisting of
the current state, the input-tape head position `p_1`, the work-tape head
position `p_2`, and the contents `t` of the work tape. -/
structure LogSpaceConfig (Q : Type) (Γ : Type) where
  state : Q
  inputHeadPos : ℕ
  workHeadPos : ℕ
  workTape : ℕ → Γ

/-- The type of log-space configurations restricted so that the input head lies
in `Fin n`, the work head lies in `Fin s`, and the work tape is encoded as a
function `Fin s → Γ`. This is a finite type whenever `Q` and `Γ` are. -/
def BoundedLogSpaceConfig (Q : Type) (Γ : Type) (n s : ℕ) :=
  Q × Fin n × Fin s × (Fin s → Γ)

/-- `BoundedLogSpaceConfig Q Γ n s` is a finite type, inherited from the
product structure of its components. -/
noncomputable instance BoundedLogSpaceConfig.fintype
    (Q : Type) (Γ : Type) [Fintype Q] [Fintype Γ] (n s : ℕ) :
    Fintype (BoundedLogSpaceConfig Q Γ n s) :=
  inferInstanceAs (Fintype (Q × Fin n × Fin s × (Fin s → Γ)))

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

/-- **Immerman–Szelepcsényi Theorem.** For any space bound `f` with
`f(n) ≥ log₂ n`, the class `NSPACE(f)` is closed under complementation:
if `A ∈ NSPACE(f)` then `Aᶜ ∈ NSPACE(f)`. -/
inductive BoundedReachable {V : Type*} (G : V → V → Prop) : ℕ → V → V → Prop where
  | refl (s : V) : BoundedReachable G 0 s s
  | step {d : ℕ} {s u t : V} : BoundedReachable G d s u → G u t →
      BoundedReachable G (d + 1) s t
  | weaken {d : ℕ} {s t : V} : BoundedReachable G d s t →
      BoundedReachable G (d + 1) s t

/-- The set of vertices reachable from `s` in `G` within at most `d` steps. -/
def reachableSet {V : Type*} (G : V → V → Prop) (d : ℕ) (s : V) : Set V :=
  {u | BoundedReachable G d s u}

/-- The count `c_d = |reachableSet G d s|` of vertices reachable from `s`
within `d` steps. In the Immerman–Szelepcsényi proof this is the quantity
computed inductively by an NL machine. -/
noncomputable def reachableCount {V : Type*} (G : V → V → Prop) (d : ℕ) (s : V) : ℕ :=
  Set.ncard (reachableSet G d s)
