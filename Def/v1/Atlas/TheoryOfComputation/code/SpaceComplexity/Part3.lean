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
import Inductive.v1.Atlas.TheoryOfComputation.code.SpaceComplexity
open Computability
open TuringMachine


namespace SpaceComplexity

variable {α : Type*}

/-- The free (unquantified) variables of a QBF: the variables of the body that are not
captured by any enclosing `∃` or `∀`. -/
def QBF.freeVars : QBF → Finset ℕ
  | .body φ => φ.vars
  | .exists_ x ψ => ψ.freeVars.erase x
  | .forall_ x ψ => ψ.freeVars.erase x

/-- A QBF is fully quantified (a sentence) when it has no free variables. -/
def QBF.IsFullyQuantified (ψ : QBF) : Prop :=
  ψ.freeVars = ∅

/-- Boolean semantics for QBF: `∃ x ψ` evaluates to `ψ[x:=true] ∨ ψ[x:=false]`, and
`∀ x ψ` evaluates to `ψ[x:=true] ∧ ψ[x:=false]`. -/
def QBF.eval (σ : BoolAssignment) : QBF → Bool
  | .body φ => φ.eval σ
  | .exists_ x ψ =>
    ψ.eval (Function.update σ x true) || ψ.eval (Function.update σ x false)
  | .forall_ x ψ =>
    ψ.eval (Function.update σ x true) && ψ.eval (Function.update σ x false)

/-- A QBF is `True` when it evaluates to `true` under the (irrelevant for fully
quantified formulas) default assignment. -/
def QBF.IsTrue (ψ : QBF) : Prop :=
  ψ.eval (fun _ => false) = true

/-- The language **TQBF** = `{ψ | ψ is a fully-quantified Boolean formula that is true}`.
TQBF is the canonical PSPACE-complete problem. -/
def TQBF : Set QBF :=
  {ψ | ψ.IsFullyQuantified ∧ ψ.IsTrue}

/-- **`NP ⊆ PSPACE`** (Sipser, Lecture 17). Every NP language is in PSPACE: combine
`NP ⊆ NTIME(n^k)` with `NTIME ⊆ SPACE`. -/
def QBF.ExistsPlayerWins (σ : BoolAssignment) : QBF → Prop
  | .body φ => φ.eval σ = true
  | .exists_ x ψ =>
    ψ.ExistsPlayerWins (Function.update σ x true) ∨
    ψ.ExistsPlayerWins (Function.update σ x false)
  | .forall_ x ψ =>
    ψ.ExistsPlayerWins (Function.update σ x true) ∧
    ψ.ExistsPlayerWins (Function.update σ x false)

/-- **Reachability in at most `b` steps** (used in Savitch's theorem proof): `c₁` can
yield `c₂` in at most `b` nondeterministic steps. -/
def NTM.CanYield (M : NTM Q Γ) (c₁ c₂ : Config Q Γ) : ℕ → Prop
  | 0 => c₁ = c₂
  | (b + 1) => c₁ = c₂ ∨ ∃ c_mid : Config Q Γ, M.step c₁ c_mid ∧ M.CanYield c_mid c₂ b

end SpaceComplexity
