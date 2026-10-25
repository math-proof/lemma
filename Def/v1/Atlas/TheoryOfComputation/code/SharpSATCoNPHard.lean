/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATCoNPHard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold


namespace NPCompleteness

open TuringMachine in
/--
A language `B` is `coNP`-hard if every language `A ∈ coNP` polynomial-time
reduces to `B`. Analogous to the NP-hardness definition `∀ A ∈ NP, A ≤_P B`
from the textbook, but for the class `coNP`.
-/
def IsCoNPHard {Γ : Type} (B : Set (List Γ)) : Prop :=
  ∀ A : Set (List Γ), InCoNP A → PolyReducible A B

/--
One plus the largest variable index appearing in `φ`. This gives an upper bound
`m` such that every variable of `φ` has index `< m`.
-/
noncomputable def BoolFormula.maxVarSucc (φ : BoolFormula) : ℕ :=
  (φ.vars.sup id).succ

/-- A Boolean formula `φ` is a tautology iff `φ.eval σ = true` for every
assignment `σ`. -/
def BoolFormula.IsTautology (φ : BoolFormula) : Prop :=
  ∀ σ : BoolAssignment, φ.eval σ = true

/-- The language `TAUTOLOGY = {⟨φ⟩ | φ is a tautology}`, the canonical
coNP-complete language. -/
def TAUTOLOGY : Set BoolFormula :=
  {φ | φ.IsTautology}

end NPCompleteness
